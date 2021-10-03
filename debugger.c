#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/user.h>
#include <sys/reg.h>
#include <sys/syscall.h>   /* For SYS_write etc */
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <elfutils/libdwfl.h>
#include "debugger.h"

struct Debugger {
    pid_t child;
    DebuggerCallbacks *callbacks;
    Dwfl *dwfl;
};

static
int copy_infotable(Debugger *debugger,
                   GElf_Addr addr, StgInfoTable *infoTable)
{
    int i = 0;
    while (i < sizeof(StgInfoTable) / sizeof(long)) {
        ((long *) infoTable)[i] =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        if (errno != 0)
            return 0;
        i++;
    }
    int j = sizeof(StgInfoTable) % sizeof(long);
    if (j != 0) {
        long val =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        if (errno != 0)
            return 0;
        memcpy(((long *) infoTable)+i, &val, j);
    }
    return 1;
}

static uint32_t
debugger_closure_sizeW(Debugger *debugger,
                       GElf_Addr addr, const StgInfoTable *infoTable)
{
    switch (infoTable->type) {
    case FUN:
    case CONSTR:
    case THUNK_STATIC:
    case IND_STATIC:
    case BLOCKING_QUEUE:
    case BLACKHOLE:
    case MVAR_CLEAN:
    case MVAR_DIRTY:
    case MUT_VAR_CLEAN:
    case MUT_VAR_DIRTY:
    case WEAK:
       return sizeofW(StgClosure)
             + sizeofW(StgPtr)  * infoTable->layout.payload.ptrs
             + sizeofW(StgWord) * infoTable->layout.payload.nptrs;
    case THUNK_0_1:
    case THUNK_1_0:
        return sizeofW(StgThunk) + 1;
    case FUN_0_1:
    case CONSTR_0_1:
    case FUN_1_0:
    case CONSTR_1_0:
        return sizeofW(StgHeader) + 1;
    case THUNK_0_2:
    case THUNK_1_1:
    case THUNK_2_0:
        return sizeofW(StgThunk) + 2;
    case FUN_0_2:
    case CONSTR_0_2:
    case FUN_1_1:
    case CONSTR_1_1:
    case FUN_2_0:
    case CONSTR_2_0:
        return sizeofW(StgHeader) + 2;
    case THUNK:
        return sizeofW(StgThunk)
             + sizeofW(StgPtr)  * infoTable->layout.payload.ptrs
             + sizeofW(StgWord) * infoTable->layout.payload.nptrs;
    case THUNK_SELECTOR:
        return sizeofW(StgSelector);
    case AP_STACK: {
        long size =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgAP_STACK,size),
                   NULL);
        return sizeofW(StgAP_STACK) + size;
    }
    case AP: {
        StgHalfWord hws[2];
        *((long *)hws) =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgAP,arity),
                   NULL);
        return sizeofW(StgAP) + hws[1];
    }
    case PAP: {
        StgHalfWord hws[2];
        *((long *)hws) =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgPAP,arity),
                   NULL);
        return sizeofW(StgPAP) + hws[1];
    }
    case IND:
        return sizeofW(StgInd);
    case ARR_WORDS: {
        long bytes =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgArrBytes,bytes),
                   NULL);
        return sizeofW(StgArrBytes) + ROUNDUP_BYTES_TO_WDS(bytes);
    }
    case MUT_ARR_PTRS_CLEAN:
    case MUT_ARR_PTRS_DIRTY:
    case MUT_ARR_PTRS_FROZEN_CLEAN:
    case MUT_ARR_PTRS_FROZEN_DIRTY: {
        long size =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgMutArrPtrs,size),
                   NULL);
        return sizeofW(StgMutArrPtrs) + size;
    }
    case SMALL_MUT_ARR_PTRS_CLEAN:
    case SMALL_MUT_ARR_PTRS_DIRTY:
    case SMALL_MUT_ARR_PTRS_FROZEN_CLEAN:
    case SMALL_MUT_ARR_PTRS_FROZEN_DIRTY: {
        long ptrs =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgSmallMutArrPtrs,ptrs),
                   NULL);
        return sizeofW(StgSmallMutArrPtrs) + ptrs;
    }
    case TSO:
        return sizeofW(StgTSO);
    case STACK: {
        long stack_size =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgStack,stack_size),
                   NULL);
        return sizeofW(StgStack) + stack_size;
    }
    case BCO: {
        StgHalfWord hws[2];
        *((long *)hws) =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr+offsetof(StgBCO,arity),
                   NULL);
        return sizeofW(StgBCO) + hws[1];
    }
    case TREC_CHUNK:
        return sizeofW(StgTRecChunk);
    default:
        return 0;
    }
}

static
StgClosure *copy_closure(Debugger *debugger,
                         GElf_Addr addr, StgInfoTable *infoTable)
{
    int size  = debugger_closure_sizeW(debugger, addr, infoTable)
                  * sizeof(StgWord);
    if (size == 0)
        return NULL;

    StgClosure *closure = malloc(size);
    if (!closure)
        return NULL;

    int i = 0;
    int count = size / sizeof(long);    
    while (i < count) {
        ((long *) closure)[i] =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        if (errno != 0) {
            free(closure);
            perror("copy_closure");
            return NULL;
        }
        i++;
    }
    int j = size % sizeof(long);
    if (j != 0) {
        long val =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        if (errno != 0) {
            free(closure);
            perror("copy_closure");
            return NULL;
        }
        memcpy(((long *) closure)+i, &val, j);
    }

    return closure;
}

static
int collect_infos(Dwfl_Module *mod, void ** x,
                  const char *name, Dwarf_Addr addr,
			      void *arg)
{
    Debugger *debugger = (Debugger *) arg;

    int n_sym = dwfl_module_getsymtab(mod);
    for (int i = 0; i < n_sym; i++) {
        GElf_Sym sym;
        GElf_Word shndx;
        GElf_Addr addr;
        Elf *elf;
        Dwarf_Addr bias;
        
        const char *name =
            dwfl_module_getsym_info(mod, i, &sym, &addr,
					    &shndx,
					    &elf, &bias);

        size_t len = strlen(name);
        if (len > 5 && strcmp(name+len-5, "_info") == 0 &&
            strcmp(name, "_dl_get_tls_static_info") != 0 &&
            strcmp(name, "version_info") != 0) {

            uint8_t int3_buf[sizeof(long)];
            *((long*) &int3_buf) =
                ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);
            uint8_t save_byte = int3_buf[0];
            int3_buf[0] = 0xCC;
            ptrace(PTRACE_POKEDATA, debugger->child, addr, *((void**) &int3_buf));

            StgInfoTable infoTable;
            if (!copy_infotable(debugger, addr - sizeof(StgInfoTable), &infoTable))
                return DWARF_CB_ABORT;

            debugger->callbacks->register_info(name,addr,save_byte,&infoTable);
        }
    }

    return DWARF_CB_OK;
}

int debugger_execv(char *pathname, char *const argv[],
                   DebuggerCallbacks* callbacks)
{
    Debugger debugger;
    debugger.callbacks = callbacks;
    debugger.dwfl = NULL;

    debugger.child = fork();
    if (debugger.child == 0) {
        ptrace(PTRACE_TRACEME, 0, NULL, NULL);
        execv(pathname, argv);
    } else {
        int state = 0;

        while(1) {
            int status;
            if (waitpid(debugger.child, &status, 0) < 0) {
                perror("waitpid");
                break;
            }
            if(WIFEXITED(status))
                break;

            struct user_regs_struct regs;
            uint8_t int3_buf[sizeof(long)];

            if (state == 0) {
                static char *debuginfo_path;
                static const Dwfl_Callbacks proc_callbacks =
                {
                    .find_debuginfo = dwfl_standard_find_debuginfo,
                    .debuginfo_path = &debuginfo_path,
                    .find_elf = dwfl_linux_proc_find_elf,
                };
                debugger.dwfl = dwfl_begin(&proc_callbacks);
                if (debugger.dwfl == NULL) {
                    return -1;
                }

                int ret = dwfl_linux_proc_report(debugger.dwfl, debugger.child);
                if (ret < 0) {
                    return -1;
                }
                
                if (dwfl_report_end(debugger.dwfl, NULL, NULL) != 0) {
                    return -1;
                }

                if (dwfl_linux_proc_attach(debugger.dwfl, debugger.child, true) < 0) {
                    return -1;
                }

                dwfl_getmodules(debugger.dwfl, collect_infos, &debugger, 0);

                state = 1;

                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
            } else if (state == 1) {
                ptrace(PTRACE_GETREGS, debugger.child, NULL, &regs);
                regs.rip--;

                StgInfoTable infoTable;
                if (!copy_infotable(&debugger, regs.rip - sizeof(StgInfoTable), &infoTable)) {
                    perror("copy_infotable");
                    exit(1);
                }

                GElf_Addr addr = (GElf_Addr) (regs.rbx & ~TAG_MASK);
                StgClosure *closure = copy_closure(&debugger, addr, &infoTable);

                uint8_t save_byte;
                if (debugger.callbacks->breakpoint_hit(&debugger, regs.rip, closure, &save_byte)) {
                    *((long*) &int3_buf) =
                        ptrace(PTRACE_PEEKDATA, debugger.child, regs.rip, NULL);
                    int3_buf[0] = save_byte;
                    ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, *((void**) &int3_buf));

                    ptrace(PTRACE_SETREGS, debugger.child, NULL, &regs);
                    ptrace(PTRACE_SINGLESTEP, debugger.child, NULL, NULL);

                    state = 2;
                } else {
                    ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
                }

                if (closure != NULL)
                    free(closure);
            } else if (state == 2) {
                *((long*) &int3_buf) =
                    ptrace(PTRACE_PEEKDATA, debugger.child, regs.rip, NULL);
                int3_buf[0] = 0xCC;
                ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, *((void**) &int3_buf));
                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);

                state = 1;
            }
        }

        if (debugger.dwfl != NULL)
            dwfl_end(debugger.dwfl);
    }
}

StgClosure *debugger_copy_closure(Debugger *debugger, GElf_Addr addr)
{
    addr = addr & ~TAG_MASK;

    GElf_Addr infoTable_addr =
        ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);

    StgInfoTable infoTable;
    if (!copy_infotable(debugger, infoTable_addr - sizeof(StgInfoTable), &infoTable))
        return NULL;

    StgClosure *closure = copy_closure(debugger, addr, &infoTable);
    if (closure == NULL) {
        closure = malloc(sizeof(StgClosure));
        closure->header.info = (StgInfoTable *)infoTable_addr;
    }
    return closure;
}
