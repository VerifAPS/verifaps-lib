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
package edu.kit.iti.formal.lsp.smv

import edu.kit.iti.formal.lsp.Highlighter
import edu.kit.iti.formal.lsp.SupportedTokenTypes
import edu.kit.iti.formal.smv.parser.SMVLexer
import edu.kit.iti.formal.smv.parser.SMVLexer.*
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import java.nio.file.Path

class SmvDocumentHighlighter : Highlighter() {
    override fun createLexer(it: String): Lexer =
        SMVLexer(org.antlr.v4.runtime.CharStreams.fromString(it))

    override fun createLexer(it: Path): Lexer =
        SMVLexer(org.antlr.v4.runtime.CharStreams.fromPath(it))

    override fun tokenModifier(token: Token): Int = 0

    override fun tokenType(token: Token): Int? = when (token.type) {
        ASSIGN, ARRAY, BOOLEAN, CASE, COMPASSION, CONSTANTS, CTLSPEC,
        DEFINE, ESAC, FAIRNESS, FROZENVAR, INIT, INVAR, INVARSPEC, ISA, IVAR, JUSTICE,
        LTLSPEC, MODULE, NAME, OF, PROCESS, PSLSPEC,
        SIGNED, SPEC, TRANS, UNSIGNED, UNION, VAR, WORD,
            -> SupportedTokenTypes.KEYWORD.ordinal

        A, X, T, U, O, S, G, H, V, Y, Z, E, F, EU, EX, EF, EG,
        BU, EBF, AG, ABF, AF, AU, AX, STAR,
        EQ, EQUIV, GT, GTE, LT, LTE, MOD, NEQ, NEXT, XNOR,
        DIV, DOT, DOTDOT, MINUS, OR, PLUS, SEMI, RPAREN,
        AND, DCOLON, LBRACKET, RBRACKET, SHIFTL, SHIFTR,
        COMMA, NOT, COLON, COLONEQ, LBRACE, RBRACE, IMP, IN, XOR
            -> SupportedTokenTypes.OPERATOR.ordinal

        NUMBER, WORD_LITERAL, FLOAT,
            TRUE, FALSE -> SupportedTokenTypes.NUMBER.ordinal

        ID -> SupportedTokenTypes.VARIABLE.ordinal

        SL_COMMENT -> SupportedTokenTypes.COMMENT.ordinal

        else -> null
    }
}