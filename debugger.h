#ifndef DEBUGGER_H
#define DEBUGGER_H

#include <Rts.h>
#include <elfutils/libdwfl.h>

typedef struct Debugger Debugger;

typedef struct {
    void (*register_info)(const char* name, GElf_Addr addr, uint8_t save_byte,
                          StgInfoTable *infoTable);
    int (*breakpoint_hit)(Debugger *debugger,
                          GElf_Addr addr, StgClosure *closure, uint8_t *save_byte);
} DebuggerCallbacks;

int debugger_execv(char *pathname, char *const argv[],
                   DebuggerCallbacks* callbacks);

StgClosure *debugger_copy_closure(Debugger *debugger, GElf_Addr addr);

#endif
