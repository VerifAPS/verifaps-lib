package edu.kit.iti.formal.automation

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.analysis.CheckForTypes
import edu.kit.iti.formal.automation.analysis.ReporterMessage
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.PouElements
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.util.*


class FlycheckArgs(parser: ArgParser) {
    val verbose by parser.flagging(help = "enable verbose mode").default(false)
    val include by parser.adding("folder for looking includes").default(arrayListOf("."))
    val files by parser.positionalList(help = "Files to check").default(arrayListOf())
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.03.18)
 */
fun main(args: Array<String>) {
    val arguments = FlycheckArgs(ArgParser(args, ArgParser.Mode.POSIX))
    main(arguments)
}

fun main(arguments: FlycheckArgs) {
    val base = BuiltinLoader.loadDefault()

    val r = FlycheckRunner(
            arguments.files.map { CharStreams.fromFileName(it) },
            base,
            arguments.verbose,
            arguments.include
    )
    r.run()
    r.messages.forEach {
        val level = Console.Level.valueOf(it.level.toUpperCase())

        Console.writeln(level,
                "(${it.sourceName}@${it.lineNumber}:${it.charInLine}) ${it.message} (${it.category})"
        )
    }
}

class FlycheckRunner(
        val streams: List<CharStream>,
        val library: PouElements = PouElements(),
        val verbose: Boolean = false,
        val includeStubs: MutableList<String> = arrayListOf()) {

    private val reporter = CheckForTypes.DefaultReporter()
    val messages: MutableList<ReporterMessage>
        get() = reporter.messages

    private val errorListener = MyAntlrErrorListener(messages)

    fun run() {
        streams.forEach { parse(it) }
        types()
    }

    fun parse(stream: CharStream) {
        val lexer = IEC61131Lexer(stream)
        val parser = IEC61131Parser(CommonTokenStream(lexer))

        lexer.removeErrorListeners()
        parser.removeErrorListeners()
        parser.addErrorListener(errorListener)
        val ctx = parser.start()
        val tles = ctx.accept(IECParseTreeToAST()) as PouElements
        library.addAll(tles)
    }

    fun types() {
        IEC61131Facade.resolveDataTypes(library)
        library.accept(CheckForTypes(reporter))
    }

    internal class MyAntlrErrorListener(private val messages: MutableCollection<ReporterMessage>)
        : ANTLRErrorListener {
        override fun syntaxError(recognizer: Recognizer<*, *>?, offendingSymbol: Any?, line: Int,
                                 charPositionInLine: Int, msg: String?, e: RecognitionException?) {
            val file = (offendingSymbol as Token?)?.tokenSource?.sourceName
            messages += ReporterMessage(file ?: "", line, charPositionInLine, msg!!, "syntax", "level")
        }

        override fun reportAttemptingFullContext(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, conflictingAlts: BitSet?, configs: ATNConfigSet?) {}
        override fun reportAmbiguity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, exact: Boolean, ambigAlts: BitSet?, configs: ATNConfigSet?) {}
        override fun reportContextSensitivity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, prediction: Int, configs: ATNConfigSet?) {}
    }
}




