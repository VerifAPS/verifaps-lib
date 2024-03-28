package edu.kit.iti.formal.stvs.model.code

import org.antlr.v4.runtime.Token

/**
 * Represents a syntax error in code.
 *
 * @author Lukas Fritsch
 */
class SyntaxError
/**
 * creates a syntax error.
 * @param line the line of the token with the syntax error
 * @param charPos the char position of the token with the syntax error
 * @param message the error message
 */(@JvmField val line: Int, val charPos: Int, @JvmField val message: String) {
    fun isToken(token: Token): Boolean {
        return (line == token.line) && (charPos == token.charPositionInLine)
    }

    override fun toString(): String {
        return "Error at ($line,$charPos): $message"
    }
}
