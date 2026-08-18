#include "Reader.h"
#include "ReadLine.h"
#include "Types.h"

#include <iostream>

malValuePtr READ(const String& input);
String PRINT(malValuePtr ast);

static String rep(const String& input);
static malValuePtr EVAL(malValuePtr ast);

int main(int, char*[])
{
    String prompt = "user> ";
    String input;
    while (s_readLine_get(prompt, input)) {
        std::cout << rep(input) << "\n";
    }
    return 0;
}

static String rep(const String& input)
{
    try {
        return PRINT(EVAL(READ(input)));
    }
    catch (malValuePtr& mv) {
        std::cerr << "Error: " << PRINT(mv) << "\n";
        return "";
    }
}

malValuePtr READ(const String& input)
{
    return readStr(input);
}

static malValuePtr EVAL(malValuePtr ast)
{
    return ast;
}

String PRINT(malValuePtr ast)
{
    return ast->print(true);
}
