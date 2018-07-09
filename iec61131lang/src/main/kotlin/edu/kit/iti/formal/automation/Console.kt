package edu.kit.iti.formal.automation

import java.io.PrintStream

/**
 * Created by weigl on 11.09.15.
 */
object Console {
    var startTime = System.currentTimeMillis()
    var currentLevel = Level.INFO
    var out: PrintStream = System.out


    enum class Level {
        DEBUG, INFO, WARN, ERROR, FATAL
    }

    fun writeTimestamp() {
        out.format("[%10.3f] ",
                (System.currentTimeMillis() - startTime) / 1000.0)
    }

    fun writeln(msg: String) {
        writeTimestamp()
        println(msg)
    }

    fun writeln(msg: () -> String) {
        writeln(msg())
    }

    fun writeln(msg: String, vararg args: Any) {
        writeln(String.format(msg, *args))
    }


    fun writeln(lvl: Level?, msg: String, vararg args: Any?) {
        val level = lvl ?: Level.INFO
        if (level.ordinal < currentLevel.ordinal) return

        writeTimestamp()
        var lString = "[%6s]".format(level)
        lString =
                when (level) {
                    Level.DEBUG -> colorizeFg(Color.Cyan, lString)
                    Level.INFO -> colorizeFg(Color.Blue, lString)
                    Level.WARN -> colorizeFg(Color.Yellow, lString)
                    Level.ERROR -> colorize(Color.Red, Color.White, lString)
                    Level.FATAL -> colorize(Color.White, Color.Red, lString)
                }
        out.println("$lString ${msg.format(args)}")
    }

    fun writeln(lvl: Level?, msg: () -> String) {
        val level = lvl ?: Level.INFO
        if (level >= currentLevel) {
            writeln(lvl, msg())
        }
    }

    fun debug(msg: String, vararg args: Any) = writeln(Level.DEBUG, msg, *args)

    fun info(msg: String, vararg args: Any) = writeln(Level.INFO, msg, *args)

    fun error(msg: String, vararg args: Any) = writeln(Level.ERROR, msg, *args)

    fun warn(msg: String, vararg args: Any) = writeln(Level.WARN, msg, *args)

    fun fatal(msg: String, vararg args: Any) = writeln(Level.FATAL, msg, *args)

    enum class Color {
        Black, Red, Green, Yellow, Blue, Magenta, Cyan, White
    }


    private val FIRST_ESC_CHAR: Char = 27.toChar()
    private val SECOND_ESC_CHAR = '['
    private val CSI = FIRST_ESC_CHAR.toString() + SECOND_ESC_CHAR
    //"\u0027["

    fun colorizeFg(color: Color, s: String) =
            "$CSI${color.ordinal + 30}m$s${CSI}0m"

    fun colorizeBg(color: Color, s: String) =
            "$CSI${color.ordinal + 40}m$s${CSI}0m"

    fun colorizeFg256(n: Int, s: String) =
            "${CSI}38;5;$n;m$s${CSI}0m"

    fun colorizeBg256(n: Int, g: Int, b: Int, s: String) =
            "${CSI}48;5;$n;m$s${CSI}0m"

    fun colorizeFgRgb(r: Int, g: Int, b: Int, s: String) =
            "${CSI}38;2;$r;$g;$b;m$s${CSI}0m"

    fun colorizeBgRgb(r: Int, g: Int, b: Int, s: String) =
            "${CSI}48;2;$r;$g;$b;m$s${CSI}0m"

    fun colorize(fg: Console.Color, bg: Console.Color, s: String) = colorizeFg(fg, colorizeBg(bg, s))
}
