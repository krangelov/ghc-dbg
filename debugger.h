#ifndef DEBUGGER_H
#define DEBUGGER_H

#include <Rts.h>
#include <elfutils/libdwfl.h>

typedef struct Debugger Debugger;

typedef struct {
    void (*register_comp_unit)(const char* comp_dir, const char* fname);
    void (*register_subprog)(const char* name);
    void (*register_scope)(int start_line,int start_col,int end_line,int end_col);
    void (*register_name)(const char* name, GElf_Addr addr, uint8_t save_byte);
    int (*breakpoint_hit)(Debugger *debugger,
                          StgInfoTable *infoTable, GElf_Addr addr,
                          StgHalfWord fun_type, StgWord *args, uint8_t *save_byte);
} DebuggerCallbacks;

int debugger_execv(char *pathname, char *const argv[],
                   DebuggerCallbacks* callbacks);

StgClosure *debugger_copy_closure(Debugger *debugger, GElf_Addr addr);

StgClosure *debugger_copy_stackframe(Debugger *debugger, size_t *offset);

void debugger_free_closure(Debugger *debugger, StgClosure *closure);

void debugger_poke(Debugger* debugger, GElf_Addr addr, uint8_t byte);

#endif
