package edu.kit.iti.formal.automation

import org.slf4j.LoggerFactory
import java.util.logging.*

enum class Color {
    Black, Red, Green, Yellow, Blue, Magenta, Cyan, White
}

/**
 * Created by weigl on 11.09.15.
 */
object Console {
    val rootLogger = LoggerFactory.getLogger("")

    val formatter = object : Formatter() {
        var startTime = System.currentTimeMillis()
        override fun format(record: LogRecord): String =
                "[%10.3f] [%6s] %s%n".format(
                        (record.millis - startTime) / 1000.0,
                        when (record.level) {
                            Level.FINE -> colorizeFg(Color.Cyan, record.level.name)
                            Level.FINER -> colorizeFg(Color.Cyan, record.level.name)
                            Level.FINEST -> colorizeFg(Color.Cyan, record.level.name)
                            Level.INFO -> colorizeFg(Color.Blue, record.level.name)
                            Level.WARNING -> colorizeFg(Color.Yellow, record.level.name)
                            Level.SEVERE -> colorize(Color.Red, Color.White, record.level.name)
                            else -> record.level.name
                        }, record.message)
    }

    fun configureLoggingConsole() {
        val logger = Logger.getLogger("")
        val handler = StreamHandler(System.out, formatter)
        logger.handlers.forEach(logger::removeHandler)
        logger.addHandler(handler)
        handler.flush()
    }

    fun debug(msg: String, vararg args: Any?) = rootLogger.debug(msg, *args)

    fun info(msg: String, vararg args: Any?) = rootLogger.info(msg, *args)

    fun error(msg: String, vararg args: Any?) = rootLogger.error(msg, *args)

    fun warn(msg: String, vararg args: Any?) = rootLogger.warn(msg, *args)

    fun fatal(msg: String, vararg args: Any?) = rootLogger.error(msg, *args)

    private val FIRST_ESC_CHAR: Char = 27.toChar()
    private val SECOND_ESC_CHAR = '['
    private val CSI = FIRST_ESC_CHAR.toString() + SECOND_ESC_CHAR


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

    fun colorize(fg: Color, bg: Color, s: String) = colorizeFg(fg, colorizeBg(bg, s))
    fun writeln(s: String) = info(s)
}


