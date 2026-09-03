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
package edu.kit.iti.formal.lsp.st

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.lsp.Highlighter
import edu.kit.iti.formal.lsp.SupportedTokenTypes
import edu.kit.iti.formal.automation.parser.IEC61131Lexer.*
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import java.nio.file.Path

class StDocumentHighlighter : Highlighter() {
    override fun createLexer(it: String): Lexer =
        IEC61131Lexer(CharStreams.fromString(it))

    override fun createLexer(it: Path): Lexer =
        IEC61131Lexer(CharStreams.fromPath(it))

    override fun tokenModifier(token: Token): Int = 0

    override fun tokenType(token: Token): Int? = when (token.type) {
        // Keywords - IEC 61131-3 standard types and keywords
        FBD_CODE, IL_CODE, SPECIAL, BLOCK_START, BLOCK_END,
        ANY, ANY_BIT, ANY_DATE, ANY_DERIVED, ANY_ELEMENTARY, ANY_INT, ANY_MAGNITUDE,
        ANY_NUM, ANY_REAL, ANY_STRING, ARRAY, BOOL, BYTE, DATE_AND_TIME, DINT, DWORD, 
        INT, LINT, LREAL, LWORD, REAL, SINT, STRING, TIME, TIME_OF_DAY, UDINT, UINT, 
        ULINT, USINT, WORD, WSTRING, POINTER, VAR_OUTPUT, AT, BY, CASE, CONFIGURATION, 
        CONSTANT, DATE, DO, DT, ELSE, ELSEIF, UNDERSCORE, END_CASE, END_CONFIGURATION, 
        END_FOR, END_FUNCTION, END_FUNCTION_BLOCK, END_IF, END_PROGRAM, END_REPEAT, 
        END_RESOURCE, END_STRUCT, END_TYPE, END_VAR, END_WHILE, EXIT, FOR, FUNCTION, 
        FUNCTION_BLOCK, F_EDGE, IF, INTERVAL, JMP, NIL, NON_RETAIN, OF, PRIORITY, 
        PROGRAM, READ_ONLY, READ_WRITE, REPEAT, RESOURCE, RETAIN, RETURN, R_EDGE, 
        SINGLE, STRUCT, TASK, THEN, TO, TYPE, UNTIL, VAR, VAR_ACCESS, VAR_CONFIG, 
        VAR_EXTERNAL, VAR_GLOBAL, VAR_INPUT, VAR_IN_OUT, VAR_TEMP, WHILE, WITH, AND,
        
        // Object-oriented extensions
        NAMESPACE, END_NAMESPACE, USING, PERSISTENT, INTERFACE, END_INTERFACE, METHOD,
        END_METHOD, CLASS, END_CLASS, OVERRIDE, FINAL, ABSTRACT, IMPLEMENTS, PUBLIC,
        INTERNAL, PROTECTED, PRIVATE, SUPER, THIS, EXTENDS, REF_TO, STEP, END_STEP,
        INITIAL_STEP, ACTION, END_ACTION, FROM, END_TRANSITION, TRANSITION,
        
        // IL instructions
        IL_ADD, IL_ANDN, IL_CAL, IL_CALC, IL_CALCN, IL_CD, IL_CLK, IL_CU, IL_DIV, IL_EQ,
        IL_GE, IL_GT, IL_IN, IL_JMP, IL_JMPC, IL_JMPCN, IL_LD, IL_LDN, IL_LE, IL_LT,
        IL_MOD, IL_MUL, IL_NE, IL_NOT, IL_ORN, IL_PT, IL_PV, IL_R1, IL_R, IL_RET, IL_RETC,
        IL_RETCN, IL_S1, IL_S, IL_ST, IL_STN, IL_STQ, IL_SUB, IL_XORN, EOL, IL_OR ->
            SupportedTokenTypes.KEYWORD.ordinal
        
        // Operators
        ARROW_RIGHT, ASSIGN, RASSIGN, ASSIGN_ATTEMPT, COMMA, DIV, EQUALS, GREATER_EQUALS,
        GREATER_THAN, LBRACE, RBRACE, LBRACKET, LESS_EQUALS, LESS_THAN, LPAREN, MINUS,
        MOD, MULT, NOT, NOT_EQUALS, OR, PLUS, POWER, RBRACKET, RPAREN, XOR, AMPERSAND,
        DOT, COLON, DCOLON, RIGHTARROW, CARET, REF, RANGE, CAST_LITERAL, NULL,
        SEMICOLON, SQUOTE -> SupportedTokenTypes.OPERATOR.ordinal
        
        // Numbers and literals
        INTEGER_LITERAL, BITS_LITERAL, REAL_LITERAL, TIME_LITERAL, DATE_LITERAL,
        TOD_LITERAL, DATETIME, INCOMPL_LOCATION_LITERAL -> SupportedTokenTypes.NUMBER.ordinal
        
        // Strings
        STRING_LITERAL, WSTRING_LITERAL -> SupportedTokenTypes.STRING.ordinal
        
        // Variables/Identifiers
        IDENTIFIER, DIRECT_VARIABLE_LITERAL -> SupportedTokenTypes.VARIABLE.ordinal
        
        // Comments
        COMMENT, LINE_COMMENT -> SupportedTokenTypes.COMMENT.ordinal
        
        else -> null
    }
}