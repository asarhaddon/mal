#include "Debug.h"
#include "ReadLine.h"

#include <readline/readline.h>
#include <readline/history.h>
#include <readline/tilde.h>

// make CPPFLAGS=-DDEBUG_READLINE

char* historyPath = NULL;
int newLines = 0;

void finalize()
{
    int err = append_history(newLines, historyPath);
    if (err == 0) {
#if DEBUG_READLINE
        TRACE("Written %d line(s) to '%s'\n", newLines, historyPath);
#endif
    }
    else {
        TRACE("Error %d while appending to '%s'\n", err, historyPath);
    }
    free(historyPath);
}

void initialize()
{
    atexit(finalize);

    historyPath = tilde_expand("~/.mal-history");

    int e1 = read_history(historyPath);
    if (e1 == 0) {
#if DEBUG_READLINE
        TRACE("Read '%s'\n", historyPath);
#endif
    }
    else if (e1 == ENOENT) {
        int e2 = write_history(historyPath);
        if (e2 == 0) {
#if DEBUG_READLINE
            TRACE("Created '%s'\n", historyPath);
#endif
        }
        else {
            TRACE("Error %d while creating '%s'\n", e2, historyPath);
        }
    }
    else {
        TRACE("Error %d while reading '%s'\n", e1, historyPath);
    }
}

bool s_readLine_get(const String& prompt, String& out)
{
    if (historyPath == NULL) {
        initialize();
    }

    char *line = readline(prompt.c_str());
    if (line == NULL) {
        return false;
    }
    add_history(line); // Add input to in-memory history
    ++newLines;

    out = line;
    free(line);

    return true;
}
