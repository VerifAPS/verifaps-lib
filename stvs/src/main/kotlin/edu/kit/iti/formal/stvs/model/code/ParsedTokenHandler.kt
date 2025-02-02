package edu.kit.iti.formal.stvs.model.code

import org.antlr.v4.runtime.Token

/**
 * A `ParsedTokenHandler` gets invoked by
 * [ParsedCode.parseCode].
 * to notify about lexed tokens.
 * Invariant: All tokens concatenated (re)produce the source code.
 */
fun interface ParsedTokenHandler {
    /**
     * This method must handle the list of tokens generated while parsing code.
     *
     * @param tokenList List of lexed tokens
     */
    fun accept(tokenList: List<Token>)
}
