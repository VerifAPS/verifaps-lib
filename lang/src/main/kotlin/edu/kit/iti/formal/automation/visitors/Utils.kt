package edu.kit.iti.formal.automation.visitors

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */


import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token


fun findProgram(tles: PouElements): ProgramDeclaration? = tles.findFirstProgram()
fun PouElements.findFirstProgram(): ProgramDeclaration? = asSequence().filterIsInstance<ProgramDeclaration>().firstOrNull()
fun selectByName(name: String) = { elements: PouElements -> elements.find { it.name == name } as? PouExecutable? }

/**
 * Created by weigla on 09.06.2014.*/
object Utils {

    fun compareTokens(tokens: List<Token>, expected: Array<String>, lexer: Lexer) {
        try {
            for (i in expected.indices) {
                val expect = lexer.getTokenType(expected[i])
                val tok = tokens[i]
                val tokName = IEC61131Lexer.tokenNames[tok.type]

                if (!expected[i].contentEquals(tokName)) {
                    throw AssertionError(
                            String.format("Token mismatch! Expected: %s but got %s", expected[i], tokName))
                }
            }
        } catch (e: IndexOutOfBoundsException) {
            throw AssertionError("Not enough tokens found!")
        }

        if (expected.size < tokens.size) {
            throw AssertionError("Too much tokens found!")
        }
    }
}
