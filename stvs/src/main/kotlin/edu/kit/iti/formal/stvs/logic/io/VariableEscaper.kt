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
package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.stvs.model.code.Code
import java.util.regex.Pattern

/**
 * This class is used to escape identifiers for the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 * @author Alexander Weigl
 */
@Deprecated("Disabled due to bugs with enum constant.")
object VariableEscaper {
    private val NUMBER_PATTERN: Pattern = Pattern.compile("-?[0-9]+")
    private val BOOL_PATTERN: Pattern = Pattern.compile("(TRUE)|(FALSE)")
    private const val PREFIX = "var_"

    /**
     * Prepends an escaping prefix to a given identifier.
     *
     * @param identifier identifier that should be escaped.
     * @return escaped identifier
     */
    fun escapeIdentifier(identifier: String): String {
        return identifier

        /*if (!NUMBER_PATTERN.matcher(identifier).matches()
        && !BOOL_PATTERN.matcher(identifier).matches()) {
      return PREFIX + identifier;
    }
    return identifier;*/
    }

    /**
     * Escapes an expression that can be parsed by ANTLR.
     *
     * @param expr expression to be escaped.
     * @return escaped expression
     */
    fun escapeCellExpression(expr: String): String {
        return expr
        /*CharStream charStream = new ANTLRInputStream(expr);
    CellExpressionLexer lexer = new CellExpressionLexer(charStream);
    String result = expr;
    int currentOffset = 0;
    for (Token token : lexer.getAllTokens()) {
      if (token.getType() == CellExpressionLexer.IDENTIFIER) {
        int begin = token.getStartIndex() + currentOffset;
        int end = token.getStopIndex() + currentOffset;
        String before = result.substring(0, begin);
        String after = result.substring(end + 1, result.length());
        result = before + PREFIX + token.getText() + after;
        currentOffset += PREFIX.length();
      }
    }
    return result;*/
    }

    /**
     * Escapes code by lexing it and treating identifiers accordingly.
     *
     * @param code code that should be escaped
     * @return escaped code
     */
    fun escapeCode(code: Code): String {
        val res = StringBuilder("")
        for (token in code.tokens) {
            if (token.type == IEC61131Lexer.IDENTIFIER) {
                res.append(escapeIdentifier(token.text))
            } else if (token.type == IEC61131Lexer.CAST_LITERAL) {
                res.append(escapeEnumReference(token.text))
            } else {
                res.append(token.text)
            }
        }
        return res.toString()
    }

    private fun escapeEnumReference(tokenText: String): String {
        val tokens = tokenText.split("#".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
        if (tokens.size != 2) {
            return escapeIdentifier(tokenText)
        }
        return escapeIdentifier(tokens[0]) + "#" + escapeIdentifier(tokens[1])
    }

    /**
     * Removes escaping from an identifier.
     *
     * @param varName identifier from which the escaping should be removed.
     * @return unescaped identifier
     */
    fun unescapeIdentifier(varName: String): String {
        if (varName.startsWith(PREFIX)) {
            return varName.substring(PREFIX.length)
        }
        return varName
    }
}