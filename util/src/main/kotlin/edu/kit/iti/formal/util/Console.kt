package edu.kit.iti.formal.util

import java.util.logging.Level
import kotlin.system.exitProcess

var currentDebugLevel = 0

enum class ConsoleColor {
    Black, Red, Green, Yellow, Blue, Magenta, Cyan, White
}

private val startTime = System.currentTimeMillis()
private val format = "[%10.3f] (%s) %s [%6s]%n"

fun printConsole(level: Level, message: String, origin: String) {
    val l = when(level) {
        Level.FINE -> 1
        Level.FINER -> 2
        Level.FINEST -> 3
        else -> 0
    }

    if(l> currentDebugLevel) return

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

    System.out.format(format, diffTime,
            level,
            colorizeFg(color, message),
            colorizeFg(ConsoleColor.Yellow, origin))
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


fun colorizeFg(color: ConsoleColor, s: String) =
        "$CSI${color.ordinal + 30}m$s${CSI}0m"

fun colorizeBg(color: ConsoleColor, s: String) =
        "$CSI${color.ordinal + 40}m$s${CSI}0m"

fun colorizeFg256(n: Int, s: String) =
        "${CSI}38;5;$n;m$s${CSI}0m"

fun colorizeBg256(n: Int, g: Int, b: Int, s: String) =
        "${CSI}48;5;$n;m$s${CSI}0m"

fun colorizeFgRgb(r: Int, g: Int, b: Int, s: String) =
        "${CSI}38;2;$r;$g;$b;m$s${CSI}0m"

fun colorizeBgRgb(r: Int, g: Int, b: Int, s: String) =
        "${CSI}48;2;$r;$g;$b;m$s${CSI}0m"

fun colorize(fg: ConsoleColor, bg: ConsoleColor, s: String) = colorizeFg(fg, colorizeBg(bg, s))
fun writeln(s: String) = info(s)


