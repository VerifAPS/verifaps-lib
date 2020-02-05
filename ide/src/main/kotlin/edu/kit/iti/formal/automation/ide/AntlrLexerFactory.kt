package edu.kit.iti.formal.automation.ide

import org.antlr.v4.runtime.Lexer


interface AntlrLexerFactory {
    fun create(code: String): Lexer
}


