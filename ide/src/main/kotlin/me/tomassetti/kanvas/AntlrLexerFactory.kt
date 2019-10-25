package me.tomassetti.kanvas

import org.antlr.v4.runtime.Lexer


interface AntlrLexerFactory {
    fun create(code: String): Lexer
}


