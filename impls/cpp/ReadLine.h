#pragma once

#include "String.h"

class ReadLine {
public:
    ReadLine(const String& historyFile);
    ~ReadLine();

    bool get(const String& prompt, String& line);

private:
    String m_historyPath;
};
