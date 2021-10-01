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

typedef struct {
    pid_t child;
    DebuggerCallbacks *callbacks;
    Dwfl *dwfl;
} Debugger;

char int3_buf[sizeof(void*)] = {0xCC};

static
void copy_infotable(Debugger *debugger,
                    GElf_Addr addr, StgInfoTable *infoTable)
{
    int i = 0;
    while (i < sizeof(StgInfoTable) / sizeof(long)) {
        ((long *) infoTable)[i] =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        i++;
    }
    int j = sizeof(StgInfoTable) % sizeof(long);
    if (j != 0) {
        long val =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        memcpy(((long *) infoTable)+i, &val, j);
    }
}

static
void *copy_closure(Debugger *debugger,
                   GElf_Addr addr, StgInfoTable *infoTable)
{
    int size =
        (infoTable->layout.payload.ptrs +
         infoTable->layout.payload.nptrs) * sizeof(StgWord);
    int count = size / sizeof(long);

    void *closure = malloc(size);
    if (!closure)
        return NULL;

    addr += sizeof(StgHeader);

    int i = 0;
    while (i < count) {
        ((long *) closure)[i] =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
        i++;
    }
    int j = size % sizeof(long);
    if (j != 0) {
        long val =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + i * sizeof(long),
                   NULL);
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
            long save_word =
                ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);
            ptrace(PTRACE_POKEDATA, debugger->child, addr, *((void**) &int3_buf));

            StgInfoTable infoTable;
            copy_infotable(debugger, addr - sizeof(StgInfoTable), &infoTable);

            debugger->callbacks->register_info(name,addr,save_word,&infoTable);
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
        int initilized = 0;

        while(1) {
            int status;
            wait(&status);
            if(WIFEXITED(status))
                break;

            if (!initilized) {
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

                initilized = 1;

                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
            } else {
                struct user_regs_struct regs;
                ptrace(PTRACE_GETREGS, debugger.child, NULL, &regs);
                regs.rip--;

                StgInfoTable infoTable;
                copy_infotable(&debugger, regs.rip - sizeof(StgInfoTable), &infoTable);

                void *closure = NULL;
                if (infoTable.type == CONSTR ||
                    infoTable.type == CONSTR_1_0 ||
                    infoTable.type == CONSTR_0_1 ||
                    infoTable.type == CONSTR_2_0 ||
                    infoTable.type == CONSTR_1_1 ||
                    infoTable.type == CONSTR_0_2 ||
                    infoTable.type == FUN ||
                    infoTable.type == FUN_1_0 ||
                    infoTable.type == FUN_0_1 ||
                    infoTable.type == FUN_2_0 ||
                    infoTable.type == FUN_1_1 ||
                    infoTable.type == FUN_0_2 ||
                    infoTable.type == THUNK ||
                    infoTable.type == THUNK_1_0 ||
                    infoTable.type == THUNK_0_1 ||
                    infoTable.type == THUNK_2_0 ||
                    infoTable.type == THUNK_1_1 ||
                    infoTable.type == THUNK_0_2 ||
                    infoTable.type == THUNK_STATIC ||
                    infoTable.type == THUNK_SELECTOR ||
                    infoTable.type == AP ||
                    infoTable.type == PAP ||
                    infoTable.type == AP_STACK ||
                    infoTable.type == IND ||
                    infoTable.type == IND_STATIC ||
                    infoTable.type == BLOCKING_QUEUE ||
                    infoTable.type == BLACKHOLE ||
                    infoTable.type == MVAR_CLEAN ||
                    infoTable.type == MVAR_DIRTY ||
                    infoTable.type == ARR_WORDS ||
                    infoTable.type == MUT_ARR_PTRS_CLEAN ||
                    infoTable.type == MUT_ARR_PTRS_DIRTY || 
                    infoTable.type == MUT_ARR_PTRS_FROZEN_DIRTY ||
                    infoTable.type == MUT_ARR_PTRS_FROZEN_CLEAN ||
                    infoTable.type == MUT_VAR_CLEAN ||
                    infoTable.type == MUT_VAR_DIRTY ||
                    infoTable.type == WEAK ||
                    infoTable.type == SMALL_MUT_ARR_PTRS_CLEAN ||
                    infoTable.type == SMALL_MUT_ARR_PTRS_DIRTY || 
                    infoTable.type == SMALL_MUT_ARR_PTRS_FROZEN_DIRTY ||
                    infoTable.type == SMALL_MUT_ARR_PTRS_FROZEN_CLEAN) {

                    GElf_Addr addr = (GElf_Addr) (regs.rbx & ~0b111);
                    closure = copy_closure(&debugger, addr, &infoTable);
                }

                long save_word;
                if (debugger.callbacks->breakpoint_hit(regs.rip, closure, &save_word)) {
                    ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, (void*)save_word);
                    ptrace(PTRACE_SETREGS, debugger.child, NULL, &regs);
                    ptrace(PTRACE_SINGLESTEP, debugger.child, NULL, NULL);
                    ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, *((void**) &int3_buf));
                }

                if (closure != NULL)
                    free(closure);

                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
            }
        }

        if (debugger.dwfl != NULL)
            dwfl_end(debugger.dwfl);
    }
}
