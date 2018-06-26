package edu.kit.iti.formal.automation

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.analysis.CheckForTypes
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.st.ast.PouElements
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.03.18)
 */
object Flycheck {

    @JvmStatic
    fun main(args: Array<String>) {
        val arguments = FlycheckArgs(ArgParser(args, ArgParser.Mode.POSIX))

        arguments.files.forEach {
            val lexer = IEC61131Lexer(CharStreams.fromFileName(it))
            val parser = IEC61131Parser(CommonTokenStream(lexer))

            lexer.removeErrorListeners()
            parser.removeErrorListeners()

            val errorListener = MyAntlrErrorListener(it)
            parser.addErrorListener(errorListener)
            val myReporter = object : CheckForTypes.Reporter {
                override fun report(position: Position, msg: String, category: String, error: String) {
                    Flycheck.print(it, position.lineNumber, position.charInLine, msg, category, error)
                }
            }

            val ctx = parser.start()
            val tles = ctx.accept(IECParseTreeToAST()) as PouElements
            IEC61131Facade.resolveDataTypes(tles)
            tles.accept(CheckForTypes(myReporter))
        }

    }

    fun print(file: String, line: Int, charInLine: Int,
              message: String, category: String, level: String) {
        System.out.println("[$level] $file:$line:$charInLine $message [$category]")
    }
}

class MyAntlrErrorListener(val file: String) : ANTLRErrorListener {
    override fun syntaxError(recognizer: Recognizer<*, *>?, offendingSymbol: Any?, line: Int,
                             charPositionInLine: Int, msg: String?, e: RecognitionException?) {
        Flycheck.print(file, line, charPositionInLine, msg!!, "syntax", "error")
    }

    override fun reportAttemptingFullContext(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, conflictingAlts: BitSet?, configs: ATNConfigSet?) {}
    override fun reportAmbiguity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, exact: Boolean, ambigAlts: BitSet?, configs: ATNConfigSet?) {}
    override fun reportContextSensitivity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, prediction: Int, configs: ATNConfigSet?) {}
}


class FlycheckArgs(parser: ArgParser) {
    val verbose by parser.flagging(help = "enable verbose mode").default(false)
    val include by parser.adding("folder for looking includes").default(arrayListOf("."))
    val files by parser.positionalList(help = "Files to check")
}
