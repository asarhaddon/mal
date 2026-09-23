class Mal.Main : GLib.Object {
    static bool eof;

    static construct {
        eof = false;
    }

    public static string? READ() {
        string? line = Readline.readline("user> ");
        if (line != null) {
            if (line.length > 0)
                Readline.History.add(line);
            return line;
        } else {
            stdout.printf("\n");
            eof = true;
            return null;
        }
    }

    public static string EVAL(string expr) {
        return expr;
    }

    public static void PRINT(string value) {
        stdout.printf("%s\n", value);
    }

    public static void rep() {
        string? val = READ();
        if (val != null) {
            val = EVAL(val);
            PRINT(val);
        }
    }

    public static int main(string[] args) {
        while (!eof) {
            rep();
        }

        return 0;
    }
}
