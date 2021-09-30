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

typedef struct Breakpoint {
    const char *name;
    GElf_Addr addr;
    long save_word;
    struct Breakpoint *next;
} Breakpoint;

typedef struct {
    pid_t child;
    Breakpoint *breakpoints;
} Debugger;

char int3_buf[sizeof(void*)] = {0xCC};

int callback(Dwfl_Module *mod, void ** x,
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
        if (len > 5 && strcmp(name+len-5, "_info") == 0) {
            Breakpoint *breakpoint = malloc(sizeof(Breakpoint));
            breakpoint->name = name;
            breakpoint->addr = addr;
            breakpoint->next = debugger->breakpoints;
            debugger->breakpoints = breakpoint;

            breakpoint->save_word =
                ptrace(PTRACE_PEEKDATA, debugger->child, addr, NULL);
            ptrace(PTRACE_POKEDATA, debugger->child, addr, *((void**) &int3_buf));
        }
    }

    return DWARF_CB_OK;
}

int main()
{
    Debugger debugger;
    debugger.breakpoints = NULL;

    debugger.child = fork();
    if (debugger.child == 0) {
        ptrace(PTRACE_TRACEME, 0, NULL, NULL);
        execl("fib", "fib", NULL);
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
                Dwfl *dwfl = dwfl_begin(&proc_callbacks);
                if (dwfl == NULL) {
                    printf("dwfl_begin failed\n");
                    return -1;
                }

                int ret = dwfl_linux_proc_report(dwfl, debugger.child);
                if (ret < 0) {
                    printf("dwfl_linux_proc_report failed\n");
                    return -1;
                }
                
                if (dwfl_report_end(dwfl, NULL, NULL) != 0) {
                    printf("dwfl_report_end failed\n");
                    return -1;
                }

                if (dwfl_linux_proc_attach(dwfl, debugger.child, true) < 0) {
                    printf("dwfl_linux_proc_attach failed\n");
                    return -1;
                }

                dwfl_getmodules(dwfl, callback, &debugger, 0);

                initilized = 1;

                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
            } else {
                struct user_regs_struct regs;
                ptrace(PTRACE_GETREGS, debugger.child, NULL, &regs);
                regs.rip--;

                Breakpoint *breakpoint = debugger.breakpoints;
                while (breakpoint != NULL) {
                    if (breakpoint->addr == regs.rip) {
                        printf("%s\n", breakpoint->name);

                        ptrace(PTRACE_POKEDATA, debugger.child, breakpoint->addr, (void*)breakpoint->save_word);
                        ptrace(PTRACE_SETREGS, debugger.child, NULL, &regs);
                        ptrace(PTRACE_SINGLESTEP, debugger.child, NULL, NULL);
                        ptrace(PTRACE_POKEDATA, debugger.child, breakpoint->addr, *((void**) &int3_buf));
                        break;
                    }
                    breakpoint = breakpoint->next;
                }
                ptrace(PTRACE_CONT, debugger.child, NULL, NULL);
            }
        }
    }
    return 0;
}
