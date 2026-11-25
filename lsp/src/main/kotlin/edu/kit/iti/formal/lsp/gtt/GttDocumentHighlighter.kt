/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.lsp.gtt

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer.*
import edu.kit.iti.formal.lsp.Highlighter
import edu.kit.iti.formal.lsp.SupportedTokenTypes
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import java.nio.file.Path

class GttDocumentHighlighter : Highlighter() {
    override fun createLexer(it: String): Lexer =
        TestTableLanguageLexer(CharStreams.fromString(it))

    override fun createLexer(it: Path): Lexer =
        TestTableLanguageLexer(CharStreams.fromPath(it))

    override fun tokenModifier(token: Token): Int = 0

    override fun tokenType(token: Token): Int? = when (token.type) {
        CONTRACT, AUTOMATON, TCONST, INHERIT_FROM, OMEGA, GVAR, WITH, FUNCTION,
        VAR, AS, OF, OPTIONS, PAUSE, BACKWARD, PLAY, ROW, GROUP, STATE, INPUT,
        OUTPUT, RELATIONAL, TABLE, PFLAG, HFLAG, IF, FI, COLUMN, NEXT, ASSUME,
        ASSERT, T, F ->
            SupportedTokenTypes.KEYWORD.ordinal

        AND, OR, XOR, DIV, MOD, MULT, PLUS, MINUS, POWER, EQUALS, NOT_EQUALS,
        LESS_THAN, LESS_EQUALS, GREATER_THAN, GREATER_EQUALS, NOT, LPAREN,
        RPAREN, LBRACKET, RBRACKET, LBRACE, RBRACE, COMMA, SEMICOLON, COLON,
        DOT, ARROW_RIGHT, GUARD ->
            SupportedTokenTypes.OPERATOR.ordinal

        INTEGER, FLOAT -> SupportedTokenTypes.NUMBER.ordinal
        S -> SupportedTokenTypes.STRING.ordinal
        COMMENT, LINE_COMMENT -> SupportedTokenTypes.COMMENT.ordinal
        IDENTIFIER, FQ_VARIABLE -> SupportedTokenTypes.VARIABLE.ordinal
        else -> null
    }
}