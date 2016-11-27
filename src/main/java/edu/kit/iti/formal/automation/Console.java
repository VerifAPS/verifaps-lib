package edu.kit.iti.formal.automation;

/**
 * Created by weigl on 11.09.15.
 */
public class Console {
    public static long startTime = System.currentTimeMillis();
    private static Level currentLevel = Level.INFO;

    public static enum Level {
        DEBUG, INFO, WARN, ERROR, FATAL;
    }

    public static void writeTimestamp() {
        System.out.format("[%10.3f] ",
                (System.currentTimeMillis() - startTime)/1000.0);
    }

    public static void writeln(String msg) {
        writeTimestamp();
        System.out.println(msg);
    }

    public static void writeln(String msg, Object... args) {
        writeln(String.format(msg, args));
    }

    public static void writeln(Level lvl, String msg, Object... args) {
        if(lvl == null) {
            lvl = Level.INFO;
        }

        if (lvl.ordinal() >= currentLevel.ordinal()) {
            writeTimestamp();
            System.out.print(lvl + " ");
            System.out.format(msg, args);
            System.out.println();
        }
    }

    public static void debug(String msg, Object... args) {
        writeln(Level.DEBUG, msg, args);
    }

    public static void info(String msg, Object... args) {
        writeln(Level.INFO, msg, args);
    }

    public static void error(String msg, Object... args) {
        writeln(Level.ERROR, msg, args);
    }

    public static void warn(String msg, Object... args) {
        writeln(Level.WARN, msg, args);
    }


    public static void warn(String msg) {
        writeln(Level.WARN, msg);
    }


    public static void fatal(String msg, Object... args) {
        writeln(Level.FATAL, msg, args);
    }
}
