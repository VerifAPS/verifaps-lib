/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.util

import java.util.logging.Level

var currentDebugLevel = 0

enum class ConsoleColor {
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,
}

private val startTime = System.currentTimeMillis()
private val format = "[%10.3f] (%s) %s [%6s]%n"

fun printConsole(level: Level, message: String, origin: String) {
    val l = when (level) {
        Level.FINE -> 1
        Level.FINER -> 2
        Level.FINEST -> 3
        else -> 0
    }

    if (l > currentDebugLevel) return

    val curTime = System.currentTimeMillis()
    val diffTime = (curTime - startTime) / 1000.0
    val color = when (level) {
        Level.FINE -> ConsoleColor.Cyan
        Level.FINER -> ConsoleColor.Cyan
        Level.FINEST -> ConsoleColor.Cyan
        Level.INFO -> ConsoleColor.White
        Level.WARNING -> ConsoleColor.Yellow
        Level.SEVERE -> ConsoleColor.Red
        else -> ConsoleColor.Black
    }

    System.out.format(
        format,
        diffTime,
        level,
        colorizeFg(color, message),
        colorizeFg(ConsoleColor.Yellow, origin),
    )
}

fun debug(msg: String, vararg args: Any?) = printConsole(Level.FINE, String.format(msg, *args), getOrigin())
fun info(msg: String, vararg args: Any?) = printConsole(Level.INFO, String.format(msg, *args), getOrigin())
fun error(msg: String, vararg args: Any?) = printConsole(Level.SEVERE, String.format(msg, *args), getOrigin())
fun warn(msg: String, vararg args: Any?) = printConsole(Level.WARNING, String.format(msg, *args), getOrigin())
fun fail(msg: String, vararg args: Any?): Nothing = throw IllegalStateException(String.format(msg, args))

fun getOrigin(): String {
    val f = Thread.currentThread().stackTrace[3]
    return f?.fileName + ":" + f?.lineNumber
}

private val FIRST_ESC_CHAR: Char = 27.toChar()
private val SECOND_ESC_CHAR = '['
private val CSI = FIRST_ESC_CHAR.toString() + SECOND_ESC_CHAR

fun colorizeFg(color: ConsoleColor, s: String) = "$CSI${color.ordinal + 30}m$s${CSI}0m"

fun colorizeBg(color: ConsoleColor, s: String) = "$CSI${color.ordinal + 40}m$s${CSI}0m"

fun colorizeFg256(n: Int, s: String) = "${CSI}38;5;$n;m$s${CSI}0m"

fun colorizeBg256(n: Int, g: Int, b: Int, s: String) = "${CSI}48;5;$n;m$s${CSI}0m"

fun colorizeFgRgb(r: Int, g: Int, b: Int, s: String) = "${CSI}38;2;$r;$g;$b;m$s${CSI}0m"

fun colorizeBgRgb(r: Int, g: Int, b: Int, s: String) = "${CSI}48;2;$r;$g;$b;m$s${CSI}0m"

fun colorize(fg: ConsoleColor, bg: ConsoleColor, s: String) = colorizeFg(fg, colorizeBg(bg, s))
fun writeln(s: String) = info(s)