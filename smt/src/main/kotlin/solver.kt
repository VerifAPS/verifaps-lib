package edu.kit.iti.formal.smt

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */

import edu.kit.iti.formal.util.findProgram
import org.antlr.v4.runtime.CharStreams
import java.io.File
import java.io.Reader
import java.io.Writer
import java.util.concurrent.TimeUnit

interface SmtSolver {
    fun send(sexpr: String)
    fun send(sexpr: SExpr) = send(sexpr.toString())
    fun send(sexpr: Collection<SExpr>) {
        sexpr.forEach { send(it) }
    }

    fun read(): SExpr
}

interface InteractiveSmtSolver : SmtSolver {
    fun start()
    fun dispose()
}

interface CliSmtSolver : SmtSolver {
    fun run(timeout: Long, unit: TimeUnit)
    fun readAll(): List<SExpr>
}

class CliSmtSolverImpl(
        val smtFile: File = File.createTempFile("verifaps_", ".smt2"),
        val command: Array<String>) : CliSmtSolver {
    val out = smtFile.bufferedWriter()
    var smtOut: Reader? = null

    companion object {
        fun getZ3(): CliSmtSolverImpl {
            val z3 = findProgram("z3")
                    ?: throw IllegalStateException("Could not find z3 in \$PATH.")
            return CliSmtSolverImpl(command = arrayOf(z3.absolutePath, "-smt2"))
        }
    }

    override fun send(sexpr: String) {
        out.write(sexpr + "\n")
    }

    override fun read(): SExpr {
        val s = smtOut ?: throw IllegalStateException("SMT process not started before read.")
        val reader = readFirstSexpr(s)
        return SExprFacade.parseExpr(CharStreams.fromString(reader))
    }

    override fun run(timeout: Long, unit: TimeUnit) {
        out.close()
        val pb = ProcessBuilder(*command, smtFile.absolutePath)
                .redirectErrorStream(true)

        val process = pb.start()

        smtOut = process.inputStream.reader()
        process.waitFor(timeout, unit)
    }

    override fun readAll(): List<SExpr> {
        val s = smtOut ?: throw IllegalStateException("SMT process not started before read.")
        val text = s.readText()
        return SExprFacade.parse(CharStreams.fromString(text))
    }
}

class TeeSolverCLI(val writeTo: Writer, val solver: InteractiveSmtSolver) : InteractiveSmtSolver {
    override fun send(sexpr: String) {
        writeTo.write(sexpr)
        writeTo.flush()
        solver.send(sexpr)
    }

    override fun read(): SExpr = solver.read().also {
        writeTo.write(it.toString())
    }

    override fun dispose() {
        solver.dispose()
        writeTo.close()
    }

    override fun start() = solver.start()
}

//taken from stvs and modified
class InteractiveSmtSolverImpl(
        var timeout: Long = 10,
        var command: Array<String> = arrayOf("z3", "-in", "-smt2")) : InteractiveSmtSolver {

    var process: Process? = null
    var smtIn: Writer? = null
    var smtOut: Reader? = null

    companion object {
        fun getZ3(): InteractiveSmtSolverImpl {
            val z3 = findProgram("z3")
                    ?: throw IllegalStateException("Could not find z3 in \$PATH.")
            return InteractiveSmtSolverImpl(command = arrayOf(z3.absolutePath, "-in", "-smt2"))
        }

    }

    override fun dispose() {
        send("(exit)")
        process?.destroyForcibly()
    }

    override fun start() {
        val processBuilder = ProcessBuilder(*command)
        process = processBuilder.start()
        smtIn = process!!.outputStream.writer()
        smtOut = process!!.inputStream.reader()
    }

    override fun send(sexpr: String) {
        val s = smtIn ?: throw IllegalStateException("SMT process not started before read.")
        with(s) {
            write(sexpr)
            flush()
        }
    }

    override fun read(): SExpr {
        val s = smtOut ?: throw IllegalStateException("SMT process not started before read.")
        val reader = readFirstSexpr(s)
        return SExprFacade.parseExpr(CharStreams.fromString(reader))
    }

    private fun quit(): Int {
        send("(exit)")
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
