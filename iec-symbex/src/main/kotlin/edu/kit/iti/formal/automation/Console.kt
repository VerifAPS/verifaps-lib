package edu.kit.iti.formal.automation

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * Created by weigl on 11.09.15.
 */
object Console {
    var startTime = System.currentTimeMillis()
    private val currentLevel = Level.INFO

    enum class Level {
        DEBUG, INFO, WARN, ERROR, FATAL
    }

    fun writeTimestamp() {
        System.out.format("[%10.3f] ",
                (System.currentTimeMillis() - startTime) / 1000.0)
    }

    fun writeln(msg: String) {
        writeTimestamp()
        println(msg)
    }

    fun writeln(msg: String, vararg args: Any) {
        writeln(String.format(msg, *args))
    }

    fun writeln(lvl: Level?, msg: String, vararg args: Any) {
        var lvl = lvl
        if (lvl == null) {
            lvl = Level.INFO
        }

        if (lvl.ordinal >= currentLevel.ordinal) {
            writeTimestamp()
            print(lvl.toString() + " ")
            System.out.format(msg, *args)
            println()
        }
    }

    fun debug(msg: String, vararg args: Any) {
        writeln(Level.DEBUG, msg, *args)
    }

    fun info(msg: String, vararg args: Any) {
        writeln(Level.INFO, msg, *args)
    }

    fun error(msg: String, vararg args: Any) {
        writeln(Level.ERROR, msg, *args)
    }

    fun warn(msg: String, vararg args: Any) {
        writeln(Level.WARN, msg, *args)
    }


    fun warn(msg: String) {
        writeln(Level.WARN, msg)
    }


    fun fatal(msg: String, vararg args: Any) {
        writeln(Level.FATAL, msg, *args)
    }
}
