package edu.kit.iti.formal.smt

import org.antlr.v4.runtime.CharStreams
import java.io.InputStreamReader
import java.io.Reader
import java.util.concurrent.TimeUnit

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
interface SmtSolver {
    fun start(): Process
    fun send(sexpr: SExpr)
    fun send(sexpr: Collection<SExpr>) {
        sexpr.forEach { send(it) }
    }

    fun readResponse(): SExpr
}

//taken from stvs and modified
abstract class SmtSolverCLI(
        var timeout: Long = 10,
        var z3Command: Array<String> = arrayOf("z3", "-in", "-smt2"))
    : SmtSolver {
    var process: Process? = null

    override fun start(): Process {
        val processBuilder = ProcessBuilder(*z3Command)
        process = processBuilder.start()
        return process!!
    }

    override fun send(smt: SExpr) = send(smt.toString())

    fun send(smt: String) {
        val process = process
        if (process != null) {
            process.outputStream.use {
                it.write(smt.toByteArray())
                it.flush()
            }
        }
    }

    override fun readResponse(): SExpr {
        val reader = readFirstSexpr(InputStreamReader(process?.inputStream))
        return SExprFacade.parseExpr(CharStreams.fromString(reader))
    }

    private fun quit(): Int {
        send("(quit)")
        process?.waitFor(timeout, TimeUnit.SECONDS)
        try {
            val exitValue = process?.waitFor() ?: -1
            return exitValue
        } catch (e: InterruptedException) {
        }
        return -1
    }
}


internal fun readFirstSexpr(reader: Reader): String {
    val readSexpr = StringBuilder()
    var c: Int
    //consume whitespaces
    do {
        c = reader.read()
        if (Character.isWhitespace(c)) continue
        else break
    } while (true)

    //End of stream, no further reading necessary
    if (c == -1) return ""

    when {
        c.toChar() == '(' -> {
            var depth = 0
            do {
                readSexpr.append(c.toChar())
                if (c.toChar() == '(') depth++
                if (c.toChar() == ')') {
                    depth--
                    if (depth <= 0) break
                }
                c = reader.read()
            } while (c != -1)
        }

        c.toChar() == '|' -> {
            do {
                readSexpr.append(c.toChar())
                c = reader.read()
            } while (c.toChar() != '|' && c != -1)
            readSexpr.append('|')
        }

        else -> {
            do {
                readSexpr.append(c.toChar())
                c = reader.read()
            } while (!Character.isWhitespace(c) && c != -1)
        }
    }
    return readSexpr.toString()
}
