package edu.kit.iti.formal.automation.visitors

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
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
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.Cloneable
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.tree.ParseTree

import java.lang.reflect.Method
import java.util.ArrayList

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
object Utils {

    /**
     *
     * findProgram.
     *
     * @param tles a [edu.kit.iti.formal.automation.st.ast.TopLevelElements] object.
     * @return a [edu.kit.iti.formal.automation.st.ast.ProgramDeclaration] object.
     */
    fun findProgram(tles: TopLevelElements): ProgramDeclaration? {
        for (t in tles)
            if (t is ProgramDeclaration)
                return t
        return null
    }

    /**
     *
     * parseStructuredText.
     *
     * @param input a [java.lang.String] object.
     * @param rule  a [java.lang.String] object.
     * @return a [org.antlr.v4.runtime.tree.ParseTree] object.
     */
    fun parseStructuredText(input: String, rule: String): ParseTree? {
        return parseStructuredText(ANTLRInputStream(input), rule)
    }

    /**
     *
     * parseStructuredText.
     *
     * @param stream a [org.antlr.v4.runtime.ANTLRInputStream] object.
     * @param rule   a [java.lang.String] object.
     * @return a [org.antlr.v4.runtime.tree.ParseTree] object.
     */
    fun parseStructuredText(stream: ANTLRInputStream, rule: String): ParseTree? {
        try {
            val stl = IEC61131Lexer(stream)
            val cts = CommonTokenStream(stl)
            val stp = IEC61131Parser(cts)
            val clazz = stp.javaClass
            var method: Method? = null
            method = clazz.getMethod(rule)
            return method!!.invoke(stp) as ParseTree
        } catch (e: Exception) {
            return null
        }

    }

    /**
     *
     * compareTokens.
     *
     * @param tokens   a [java.util.List] object.
     * @param expected an array of [java.lang.String] objects.
     * @param lexer    a [org.antlr.v4.runtime.Lexer] object.
     */
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

    fun <T : Cloneable<T>> copy(`in`: List<T>): List<T> {
        val list = ArrayList<T>()
        `in`.forEach { a -> list.add(a.clone()) }
        return list
    }

    fun <T : Cloneable<T>> copyNull(obj: T?): T? {
        return obj?.clone()
    }
}
