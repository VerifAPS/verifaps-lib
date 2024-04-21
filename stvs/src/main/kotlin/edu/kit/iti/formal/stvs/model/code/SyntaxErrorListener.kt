package edu.kit.iti.formal.stvs.model.code

import org.antlr.v4.runtime.ANTLRErrorListener
import org.antlr.v4.runtime.Parser
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.util.*

/**
 * A listener for [SyntaxError]s in code.
 *
 * @author Lukas Fritsch
 */
class SyntaxErrorListener : ANTLRErrorListener {
    val syntaxErrors: MutableList<SyntaxError> = ArrayList()

    override fun syntaxError(
        recognizer: Recognizer<*, *>?, offendingSymbol: Any, line: Int,
        charPositionInLine: Int, msg: String, exc: RecognitionException
    ) {
        syntaxErrors.add(SyntaxError(line, charPositionInLine, msg))
    }

    override fun reportAmbiguity(
        recognizer: Parser, dfa: DFA, startIndex: Int, stopIndex: Int,
        exact: Boolean, ambigAlts: BitSet, configs: ATNConfigSet
    ) {
    }

    override fun reportAttemptingFullContext(
        recognizer: Parser, dfa: DFA, startIndex: Int, stopIndex: Int,
        conflictingAlts: BitSet, configs: ATNConfigSet
    ) {
    }

    override fun reportContextSensitivity(
        recognizer: Parser, dfa: DFA, startIndex: Int, stopIndex: Int,
        prediction: Int, configs: ATNConfigSet
    ) {
    }
}
