#ifndef DEBUGGER_H
#define DEBUGGER_H

#include <Rts.h>
#include <elfutils/libdwfl.h>

typedef struct {
    void (*register_info)(const char* name, GElf_Addr addr, long save_word,
                          StgInfoTable *infoTable);
    int (*breakpoint_hit)(GElf_Addr addr, long *save_word);
} DebuggerCallbacks;

int debugger_execv(char *pathname, char *const argv[],
                   DebuggerCallbacks* callbacks);

#endif
