#ifndef DEBUGGER_H
#define DEBUGGER_H

#include <Rts.h>
#include <elfutils/libdwfl.h>

typedef struct Debugger Debugger;

typedef struct {
    void (*register_comp_unit)(const char* comp_dir, const char* fname);
    void (*register_subprog)(const char* name);
    void (*register_scope)(int start_line,int start_col,int end_line,int end_col);
    void (*register_info)(const char* name, GElf_Addr addr, uint8_t save_byte,
                          StgInfoTable *infoTable);
    int (*breakpoint_hit)(Debugger *debugger,
                          GElf_Addr addr, size_t n_args, StgWord *args, uint8_t *save_byte);
} DebuggerCallbacks;

int debugger_execv(char *pathname, char *const argv[],
                   DebuggerCallbacks* callbacks);

StgClosure *debugger_copy_closure(Debugger *debugger, GElf_Addr addr);

#endif
