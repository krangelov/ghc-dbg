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

#define DW_TAG_subprogram 0x2e
#define DW_TAG_lexical_block 0x0b
#define DW_TAG_ghc_src_note 0x5b00

#define DW_AT_name 0x03
#define DW_AT_language 0x13
#define DW_AT_comp_dir 0x1b
#define DW_AT_linkage_name 0x6e
#define DW_AT_ghc_span_file 0x2b00
#define DW_AT_ghc_span_start_line 0x2b01
#define DW_AT_ghc_span_start_col 0x2b02
#define DW_AT_ghc_span_end_line 0x2b03
#define DW_AT_ghc_span_end_col 0x2b04

#define DW_LANG_Haskell 0x18

#define MAX_LARGE_BITMAP 128
struct StgMaxInfoTable {
    StgLargeBitmap large_bitmap;
    StgWord pad[(MAX_LARGE_BITMAP+sizeof(StgWord)*8-1)/(sizeof(StgWord)*8)];  // Enough space to support 128 arguments
    union {
      StgFunInfoTable fun;
      StgRetInfoTable ret;
      StgConInfoTable con;
      StgThunkInfoTable thunk;
    } i;
};

#define INFO_TABLE_MAX_SIZE sizeof(struct StgMaxInfoTable)

struct Debugger {
    pid_t child;
    DebuggerCallbacks *callbacks;
    Dwfl *dwfl;
    GElf_Addr rbp;
};

static
StgInfoTable *copy_infotable(Debugger *debugger,
                             GElf_Addr addr, char *buf)
{
    char *p = buf + INFO_TABLE_MAX_SIZE;

    size_t sz = sizeof(StgInfoTable);

    int i = 0;
    while (i < sz) {
        i += sizeof(long);

        *((long *) (p - i)) =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr - i,
                   NULL);
        if (errno != 0)
            return NULL;
    }

    StgInfoTable *infoTable =
        (StgInfoTable *) (buf + INFO_TABLE_MAX_SIZE - sizeof(StgInfoTable));

    bool is_fun     = false;
    switch (infoTable->type) {
    case FUN:
    case FUN_0_1:
    case FUN_0_2:
    case FUN_1_1:
    case FUN_2_0:
    case FUN_1_0:
    case FUN_STATIC:
        is_fun = true;
        sz = sizeof(StgFunInfoTable);
        break;
    case RET_BCO:
    case RET_SMALL:
    case RET_BIG:
    case RET_FUN:
        sz = sizeof(StgRetInfoTable);
        break;
    case CONSTR:
    case CONSTR_0_1:
    case CONSTR_0_2:
    case CONSTR_1_1:
    case CONSTR_2_0:
    case CONSTR_1_0:
    case CONSTR_NOCAF:
        sz = sizeof(StgConInfoTable);
        break;
    case THUNK:
    case THUNK_1_0:
    case THUNK_0_1:
    case THUNK_2_0:
    case THUNK_1_1:
    case THUNK_0_2:
    case THUNK_STATIC:
    case THUNK_SELECTOR:
        sz = sizeof(StgThunkInfoTable);
        break;
    }

    while (i < sz) {
        i += sizeof(long);

        *((long *) (p - i)) =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr - i,
                   NULL);
        if (errno != 0)
            return NULL;
    }

    StgWord *bitmap_src = NULL;
    if (is_fun) {
        StgFunInfoTable *funInfoTable =
            (StgFunInfoTable *) (buf + INFO_TABLE_MAX_SIZE - sizeof(StgFunInfoTable));
        if (funInfoTable->f.fun_type == ARG_GEN_BIG) {
            bitmap_src = ((StgWord *) addr) + funInfoTable->f.b.bitmap_offset;
            funInfoTable->f.b.bitmap_offset =
                ((StgWord*) buf)-((StgWord*) (funInfoTable+1));
        }
    } else if (infoTable->type == RET_BIG) {
        bitmap_src = ((StgWord *) addr) + infoTable->layout.large_bitmap_offset;
        infoTable->layout.large_bitmap_offset =
            ((StgWord*) buf)-((StgWord*) (infoTable+1));
    }

    if (bitmap_src != NULL) {
        StgLargeBitmap *large_bitmap = (StgLargeBitmap *) buf;

        large_bitmap->size =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   bitmap_src++,
                   NULL);
        if (errno != 0)
            return NULL;
        if (large_bitmap->size > MAX_LARGE_BITMAP)
            return NULL;

        size_t b = 0;
        for (size_t i = 0; i < large_bitmap->size; i += sizeof(StgWord)*8) {
            large_bitmap->bitmap[b++] =
                ptrace(PTRACE_PEEKDATA,
                       debugger->child,
                       bitmap_src++,
                       NULL);
            if (errno != 0)
                return NULL;
        }
    }

    return infoTable;
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
    case RET_SMALL: {
        StgWord bitmap = infoTable->layout.bitmap;
        return sizeofW(StgClosure)
             + BITMAP_SIZE(bitmap) * sizeofW(StgWord);
    }
    case RET_BCO:
    case RET_BIG:
    case RET_FUN:
        return sizeofW(StgClosure)
             + sizeofW(StgPtr)  * infoTable->layout.payload.ptrs
             + sizeofW(StgWord) * infoTable->layout.payload.nptrs;
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
    case UNDERFLOW_FRAME:
        return sizeofW(StgUnderflowFrame);
    case UPDATE_FRAME:
        return sizeofW(StgUpdateFrame);
    default:
        return 0;
    }
}

static
StgWord *save_vanila_args(Debugger *debugger,
                          StgWord r1_value,
                          struct user_regs_struct *regs,
                          size_t n_args)
{
    StgWord *args = malloc(sizeof(StgWord)*n_args);
    if (args == NULL)
        return NULL;
    StgWord *p = args;

    if (n_args > 0) *(p++) = r1_value;
    if (n_args > 1) *(p++) = regs->r14;
    if (n_args > 2) *(p++) = regs->rsi;
    if (n_args > 3) *(p++) = regs->rdi;
    if (n_args > 4) *(p++) = regs->r8;
    if (n_args > 5) *(p++) = regs->r9;
    if (n_args > 6) {
        size_t i = 6;
        while (i < n_args) {
            *(p++) =
                ptrace(PTRACE_PEEKDATA,
                       debugger->child,
                       debugger->rbp,
                       NULL);
            if (errno != 0) {
                free(args);
                return NULL;
            }
            debugger->rbp += sizeof(StgWord);
            i++;
        }
    }

    return args;
}

static
StgWord *get_args(Debugger *debugger,
                  StgInfoTable *infoTable,
                  struct user_regs_struct *regs,
                  struct user_fpregs_struct *fpregs,
                  StgHalfWord *p_fun_type)
{
    GElf_Addr r1_value = regs->rbx;
    *p_fun_type = ARG_NONE;

    switch (infoTable->type) {
    case FUN_STATIC: {
        Dwfl_Module *mod = dwfl_addrmodule(debugger->dwfl, regs->rip);
        if (mod != NULL) {
            GElf_Sym sym;
            GElf_Word shndx;
            const char *name =
                dwfl_module_addrsym(mod, regs->rip, &sym, &shndx);
            size_t len = strlen(name);
            char *closure_name = alloca(len+6);
            strcpy(closure_name, name);
            strcpy(closure_name+len-4, "closure");

            int n_sym = dwfl_module_getsymtab(mod);
            for (int i = 0; i < n_sym; i++) {
                Elf *elf;
                Dwarf_Addr bias;

                const char *curr_name =
                    dwfl_module_getsym_info(mod, i, &sym, &r1_value,
                                            &shndx,
                                            &elf, &bias);
                if (strcmp(curr_name, closure_name) == 0) {
                    break;
                }
            }
        }
        // continue
    }
    case FUN:
    case FUN_0_1:
    case FUN_0_2:
    case FUN_1_1:
    case FUN_2_0:
    case FUN_1_0: {
        StgFunInfoTable *funInfoTable = (StgFunInfoTable *)
            (((char *) infoTable) - offsetof(StgFunInfoTable,i));
        *p_fun_type = funInfoTable->f.fun_type;
        switch (funInfoTable->f.fun_type) {
        case ARG_GEN:
            return save_vanila_args(debugger,r1_value,regs,
                                    BITMAP_SIZE(funInfoTable->f.b.bitmap)+1);
        case ARG_GEN_BIG: {
            return save_vanila_args(debugger,r1_value,regs,
                                    GET_FUN_LARGE_BITMAP(funInfoTable)->size);
        }
        case ARG_BCO:
            return save_vanila_args(debugger,r1_value,regs,
                                    BCO_BITMAP_SIZE(funInfoTable)+1);
        case ARG_NONE:
            return save_vanila_args(debugger,r1_value,regs,1);
        case ARG_N:
        case ARG_P:
            return save_vanila_args(debugger,r1_value,regs,2);
        case ARG_F:
        case ARG_D: {
            StgFloat *args = malloc(sizeof(StgFloat));
            if (args == NULL)
                return NULL;
            args[0] = *((StgFloat *) fpregs->xmm_space);
            return (StgWord *) args;
        }
        case ARG_L:
        case ARG_V16:
        case ARG_V32:
        case ARG_V64:
            return save_vanila_args(debugger,r1_value,regs,1);
        case ARG_NN:
        case ARG_NP:
        case ARG_PN:
        case ARG_PP:
            return save_vanila_args(debugger,r1_value,regs,3);
        case ARG_NNN:
        case ARG_NNP:
        case ARG_NPN:
        case ARG_NPP:
        case ARG_PNN:
        case ARG_PNP:
        case ARG_PPN:
        case ARG_PPP:
            return save_vanila_args(debugger,r1_value,regs,4);
        case ARG_PPPP:
            return save_vanila_args(debugger,r1_value,regs,5);
        case ARG_PPPPP:
            return save_vanila_args(debugger,r1_value,regs,6);
        case ARG_PPPPPP:
            return save_vanila_args(debugger,r1_value,regs,7);
        case ARG_PPPPPPP:
            return save_vanila_args(debugger,r1_value,regs,8);
        case ARG_PPPPPPPP:
            return save_vanila_args(debugger,r1_value,regs,9);
        }
        break;
    }
    case CONSTR:
    case CONSTR_0_1:
    case CONSTR_0_2:
    case CONSTR_1_1:
    case CONSTR_2_0:
    case CONSTR_1_0:
    case CONSTR_NOCAF:
    case THUNK:
    case THUNK_0_1:
    case THUNK_0_2:
    case THUNK_1_1:
    case THUNK_2_0:
    case THUNK_1_0:
    case THUNK_STATIC:
    case THUNK_SELECTOR:
    case IND:
    case IND_STATIC:
    case BLACKHOLE:
    case CATCH_FRAME:
    case STOP_FRAME:
        return save_vanila_args(debugger,r1_value,regs,1);
    case RET_BCO:
    case RET_SMALL:
    case RET_BIG:
    case RET_FUN:
    case UPDATE_FRAME:
        // The stack for return frames doesn't always contain info ptr
        ptrace(PTRACE_POKEDATA, debugger->child, regs->rbp, regs->rip);
        return save_vanila_args(debugger,r1_value,regs,1);
    }

    return NULL; // should not happen
}

static
int collect_infos(Dwfl_Module *mod, void ** x,
                  const char *name, Dwarf_Addr addr,
			      void *arg)
{
    Debugger *debugger = (Debugger *) arg;


    Dwarf_Addr bias;
    Dwarf_Die *cu = NULL;
    for (;;) {
        cu = dwfl_module_nextcu(mod, cu, &bias);
        if (cu == NULL)
            break;

        Dwarf_Attribute attr;
        if (dwarf_attr(cu, DW_AT_language, &attr) != NULL &&
            *attr.valp == DW_LANG_Haskell) {

            const char *comp_dir = NULL;
            if (dwarf_attr(cu, DW_AT_comp_dir, &attr) != NULL) {
                comp_dir = attr.valp;
            }
            const char *fname = NULL;
            if (dwarf_attr(cu, DW_AT_name, &attr) != NULL) {
                fname = attr.valp;
            }
            debugger->callbacks->register_comp_unit(comp_dir,fname);

            Dwarf_Die subprog;
            int res = dwarf_child(cu, &subprog);
            while (res == 0) {
                if (dwarf_tag(&subprog) == DW_TAG_subprogram) {
                    const char *fun_name = NULL;
                    if (dwarf_attr(&subprog, DW_AT_linkage_name, &attr) != NULL) {
                         fun_name = attr.valp;
                    }

                    Dwarf_Die lexblock;
                    int res = dwarf_child(&subprog, &lexblock);
                    while (res == 0) {
                        if (dwarf_tag(&lexblock) == DW_TAG_lexical_block) {
                            Dwarf_Die node;
                            int res = dwarf_child(&lexblock, &node);
                            while (res == 0) {
                                if (dwarf_tag(&node) == DW_TAG_ghc_src_note) {
                                    int start_line = 0, start_col = 0;
                                    int end_line = 0,   end_col = 0;

                                    if (dwarf_attr(&node, DW_AT_ghc_span_start_line, &attr) != NULL) {
                                        start_line = *((int*) attr.valp);
                                    }
                                    if (dwarf_attr(&node, DW_AT_ghc_span_start_col, &attr) != NULL) {
                                        start_col = *((char*) attr.valp);
                                    }
                                    if (dwarf_attr(&node, DW_AT_ghc_span_end_line, &attr) != NULL) {
                                        end_line = *((int*) attr.valp);
                                    }
                                    if (dwarf_attr(&node, DW_AT_ghc_span_end_col, &attr) != NULL) {
                                        end_col = *((char*) attr.valp);
                                    }

                                    debugger->callbacks->register_scope(start_line,start_col,end_line,end_col);
                                }
                                res = dwarf_siblingof(&node, &node);
                            }
                        }
                        res = dwarf_siblingof(&lexblock, &lexblock);
                    }

                    debugger->callbacks->register_subprog(fun_name);
                }
                res = dwarf_siblingof(&subprog, &subprog);
            }
        }
    }

    int n_sym = dwfl_module_getsymtab(mod);
    for (int i = 0; i < n_sym; i++) {
        GElf_Sym sym;
        GElf_Word shndx;
        GElf_Addr addr;
        Elf *elf;
        
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

            debugger->callbacks->register_name(name,addr,save_byte);
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
    debugger.rbp = 0;

    debugger.child = fork();
    if (debugger.child == -1) {
        return errno;
    } else if (debugger.child == 0) {
        ptrace(PTRACE_TRACEME, 0, NULL, NULL);
        execv(pathname, argv);
        exit(127);
    } else {
        int state = 0;
        int res   = 0;

        while(1) {
            int status;
            if (waitpid(debugger.child, &status, 0) < 0) {
                res = errno;
                break;
            }
            if (WIFEXITED(status)) {
                if (WEXITSTATUS(status) == 127)
                    res = ENOENT;
                break;
            }

            struct user_regs_struct regs;
            struct user_fpregs_struct fpregs;
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
            } else if (state == 1 || state == 2) {

                if (WIFSTOPPED(status) && WSTOPSIG(status) != SIGTRAP) {
                    ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
                    continue;
                }

                ptrace(PTRACE_GETREGS, debugger.child, NULL, &regs);
                regs.rip--;

                ptrace(PTRACE_GETFPREGS, debugger.child, NULL, &fpregs);

                char buf[INFO_TABLE_MAX_SIZE];
                StgInfoTable *infoTable =
                    copy_infotable(&debugger, regs.rip, buf);
                if (infoTable == NULL) {
                    perror("copy_infotable");
                    exit(1);
                }

                StgHalfWord fun_type;
                debugger.rbp = regs.rbp;
                StgWord *args = get_args(&debugger, infoTable, &regs, &fpregs, &fun_type);

                int res;
                uint8_t save_byte;
                if (state == 2 || (res = debugger.callbacks->breakpoint_hit(&debugger, infoTable, regs.rip, fun_type, args, &save_byte)) != 0) {
                    if (res > 2) {
                        ptrace(PTRACE_KILL, debugger.child, 0, NULL);
                        break;
                    }

                    *((long*) &int3_buf) =
                        ptrace(PTRACE_PEEKDATA, debugger.child, regs.rip, NULL);
                    int3_buf[0] = save_byte;
                    ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, *((void**) &int3_buf));

                    ptrace(PTRACE_SETREGS, debugger.child, NULL, &regs);

                    if (res == 1) {
                        ptrace(PTRACE_SINGLESTEP, debugger.child, NULL, NULL);
                        state = 3;
                    } else {
                        ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
                        state = 1;
                    }
                } else {
                    ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
                }

                if (args != NULL)
                    free(args);
            } else if (state == 3) {
                *((long*) &int3_buf) =
                    ptrace(PTRACE_PEEKDATA, debugger.child, regs.rip, NULL);
                int3_buf[0] = 0xCC;
                ptrace(PTRACE_POKEDATA, debugger.child, regs.rip, *((void**) &int3_buf));
                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);

                state = 1;
                if (WIFSTOPPED(status) && WSTOPSIG(status) != SIGTRAP) {
                    state = 2;
                }
            }
        }

        if (debugger.dwfl != NULL)
            dwfl_end(debugger.dwfl);

        return res;
    }
}

static
StgClosure *copy_closure_helper(Debugger *debugger, GElf_Addr addr,
                                size_t *psize)
{
    *psize = 0;

    addr = addr & ~TAG_MASK;

    GElf_Addr infoTable_addr =
        ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);

    char buf[INFO_TABLE_MAX_SIZE];
    StgInfoTable *infoTable =
        copy_infotable(debugger, infoTable_addr, buf);
    if (infoTable == NULL)
        return NULL;

    int size = debugger_closure_sizeW(debugger, addr, infoTable)
                 * sizeof(StgWord);
    if (size == 0) {
        size = sizeof(StgClosure);
    }

    *psize = size;

    char  *name = NULL;
    size_t name_len = 0;
    if (infoTable->type == CONSTR ||
        infoTable->type == CONSTR_0_1 ||
        infoTable->type == CONSTR_0_2 ||
        infoTable->type == CONSTR_1_1 ||
        infoTable->type == CONSTR_2_0 ||
        infoTable->type == CONSTR_1_0 ||
        infoTable->type == CONSTR_NOCAF) {
            StgConInfoTable *conInfoTable =
                (StgConInfoTable *)
                    (((char*) infoTable) - offsetof(StgConInfoTable,i));
            GElf_Addr name_addr =
                infoTable_addr + conInfoTable->con_desc;
            conInfoTable->con_desc = size;

            size_t size = 0;
            for (;;) {
                if (name_len + sizeof(long) >= size) {
                    size += sizeof(long)*4;
                    name = realloc(name, size);
                }

                *((long *) (name+name_len)) =
                    ptrace(PTRACE_PEEKDATA,
                           debugger->child,
                           name_addr + name_len,
                           NULL);
                if (errno != 0) {
                    free(name);
                    perror("copy_closure");
                    return NULL;
                }

                for (size_t i = 0; i < sizeof(long); i++) {
                    if (name[name_len] == 0)
                        goto done;
                    name_len++;
                }
            }

    done:;
    }

    char *copy = malloc(sizeof(buf)+size+name_len+1);
    if (!copy) {
        free(name);
        return NULL;
    }
    memcpy(copy, buf, sizeof(buf));

    StgClosure *closure = (StgClosure*) (copy + sizeof(buf));
    size_t offs = 0;
    while (offs < size) {
        ((long *) closure)[offs/sizeof(long)] =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   addr + offs,
                   NULL);
        if (errno != 0) {
            free(name);
            free(copy);
            perror("copy_closure");
            return NULL;
        }
        offs += sizeof(long);
    }

    if (name != NULL) {
        memcpy(copy + sizeof(buf) + size, name, name_len+1);
        free(name);
    }

    return closure;
}

StgClosure *debugger_copy_closure(Debugger *debugger, GElf_Addr addr)
{
    size_t size;
    return copy_closure_helper(debugger,addr,&size);
}

StgClosure *debugger_copy_stackframe(Debugger *debugger, size_t *offset)
{
    size_t size;

again:;
    StgClosure *closure =
        copy_closure_helper(debugger,debugger->rbp+*offset,&size);
    if (closure == NULL)
        return NULL;

    StgInfoTable *infoTable =
        (StgInfoTable *) (((char*) closure) - sizeof(StgInfoTable));
    if (infoTable->type == UNDERFLOW_FRAME) {
        StgUnderflowFrame* u = (StgUnderflowFrame*)closure;
        GElf_Addr new_sp =
            ptrace(PTRACE_PEEKDATA,
                   debugger->child,
                   (long) u->next_chunk+offsetof(StgStack,sp));
        *offset=new_sp-debugger->rbp;
        goto again;
    }

    (*offset) += size;
    return closure;
}

void debugger_free_closure(Debugger *debugger, StgClosure *closure)
{
    if (closure == NULL)
        return;
    free(((char*) closure) - INFO_TABLE_MAX_SIZE);
}

void debugger_poke(Debugger* debugger, GElf_Addr addr, uint8_t byte)
{
    uint8_t int3_buf[sizeof(long)];
    *((long*) &int3_buf) =
        ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);
    int3_buf[0] = byte;
    ptrace(PTRACE_POKEDATA, debugger->child, addr, *((void**) &int3_buf));
}
