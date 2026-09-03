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
package edu.kit.iti.formal.lsp

import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import org.eclipse.lsp4j.SemanticTokenModifiers
import org.eclipse.lsp4j.SemanticTokenTypes
import org.eclipse.lsp4j.SemanticTokens
import org.eclipse.lsp4j.SemanticTokensLegend
import java.nio.file.Path

enum class SupportedTokenTypes(val kind: String) {
    COMMENT(SemanticTokenTypes.Comment),
    VARIABLE(SemanticTokenTypes.Variable),
    KEYWORD(SemanticTokenTypes.Keyword),
    STRING(SemanticTokenTypes.String),
    NUMBER(SemanticTokenTypes.Number),
    OPERATOR(SemanticTokenTypes.Operator),
    MODIFIER(SemanticTokenTypes.Modifier),
    METHOD(SemanticTokenTypes.Method),
    FUNCTION(SemanticTokenTypes.Function),
    PROPERTY(SemanticTokenTypes.Property),
    PARAMETER(SemanticTokenTypes.Parameter),
    TYPE_PARAMETER(SemanticTokenTypes.TypeParameter),
    STRUCT(SemanticTokenTypes.Struct),
    ENUM(SemanticTokenTypes.Enum),
    INTERFACE(SemanticTokenTypes.Interface),
    CLASS(SemanticTokenTypes.Class),
    TYPE(SemanticTokenTypes.Type),
}

enum class SupportedTokenModifier(val kind: String) {
    DECLARATION(SemanticTokenModifiers.Declaration),
    DOCUMENTATION(SemanticTokenModifiers.Documentation),
    DEPRECATED(SemanticTokenModifiers.Deprecated),
    STATIC(SemanticTokenModifiers.Static),
}

abstract class Highlighter {

    val tokenTypes = SupportedTokenTypes.entries.map { it.kind }
    val tokenModifiers = SupportedTokenModifier.entries.map { it.kind }
    val legend: SemanticTokensLegend = SemanticTokensLegend(tokenTypes, tokenModifiers)

    fun analyzeToken(it: String): Sequence<Token> =
        createLexer(it).asSequence()

    fun analyzeText(text: String): SemanticTokens {
        val tb = SemanticTokensBuilder()
        analyzeToken(text).forEach { token ->
            tokenType(token)?.let { tt ->
                tb.add(token.line - 1, token.charPositionInLine, token.text.length, tt, tokenModifier(token))
            }
        }
        return SemanticTokens(tb.data)
    }

    abstract fun tokenModifier(token: Token): Int
    abstract fun tokenType(token: Token): Int?
    abstract fun createLexer(it: String): Lexer
    abstract fun createLexer(it: Path): Lexer
}

/*
    There are different ways how the position of a token can be expressed in a file.
    Absolute positions or relative positions. The protocol for the token format relative uses
    relative positions, because most tokens remain stable relative to each other when edits
    are made in a file. This simplifies the computation of a delta if a server supports it.
    So each token is represented using 5 integers. A specific token i in the file consists
    of the following array indices:

    at index 5*i - deltaLine: token line number, relative to the previous token
    at index 5*i+1 - deltaStart: token start character, relative to the previous token (relative to 0 or the previous
    token’s start if they are on the same line)
    at index 5*i+2 - length: the length of the token.
    at index 5*i+3 - tokenType: will be looked up in SemanticTokensLegend.tokenTypes. We currently ask that tokenType < 65536.
    at index 5*i+4 - tokenModifiers: each set bit will be looked up in SemanticTokensLegend.tokenModifiers
 */
data class SemanticTokensBuilder(val data: ArrayList<Int> = ArrayList(4096)) {
    private var lastLineStart = 0
    private var lastColumnStart = 0

    fun add(beginLine: Int, beginColumn: Int, length: Int, tokenType: Int, modifiers: Int) {
        data.ensureCapacity(data.size + 5)
        if (beginLine != lastLineStart) {
            lastColumnStart = 0
        }

        data.add(beginLine - lastLineStart)
        data.add(beginColumn - lastColumnStart)
        data.add(length)
        data.add(tokenType)
        data.add(modifiers)

        lastLineStart = beginLine
        lastColumnStart = beginColumn
    }
}