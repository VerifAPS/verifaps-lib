package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

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
