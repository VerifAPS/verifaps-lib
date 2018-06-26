package edu.kit.iti.formal.smv.parser

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SMVExpr
import org.antlr.v4.runtime.CharStreams
import java.io.BufferedReader
import java.io.File
import java.io.IOException
import java.io.InputStreamReader
import java.util.*
import java.util.stream.Collectors

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
object TestHelper {
    fun getFile(path: String): String {
        return getFile(TestHelper::class.java, path)
    }

    fun getFile(aClass: Class<*>, path: String): String {
        return aClass.getResource(path).toExternalForm().substring(5)
    }

    fun getResourcesAsParameters(folder: String): Iterable<Array<out Any>> {
        val files = getResources(folder)
        return files.map { f -> arrayOf(f!! as Any) }
    }

    fun getResources(folder: String): Array<File> {
        val f = TestHelper::class.java.classLoader.getResource(folder)
        if (f == null) {
            System.err.format("Could not find %s%n", folder)
            return arrayOf()
        }
        val file = File(f.file)
        return file.listFiles()
    }

    @Throws(IOException::class)
    fun loadLines(filename: String, expectedArgs: Int): Iterable<Array<out Any>> {
        //val validExpression = ArrayList<Array<Any>>(4096)
        val ve = TestHelper::class.java.getResourceAsStream(filename)

        if (ve == null) {
            System.err.println("Could not find: $filename")
            return arrayListOf()
        }

        val stream = BufferedReader(InputStreamReader(ve))
        return stream.lineSequence()
                .filter { !(it.startsWith("#") || it.isEmpty()) }
                .map {
                    it.split(">>>".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
                }
                .filter {
                    val b = it.size == expectedArgs;
                    if (!b)
                        System.err.println("Line $it has ${it.size} arguments, expected $expectedArgs. SKIPPED%n");
                    b
                }
                .asIterable()

    }

    //  println("Found: " + filename + " with " + validExpression.size + " lines!")
    //  return validExpression


    fun asParameters(cases: Array<String>): Collection<Array<out Any>> {
        return cases.map { s -> arrayOf(s) }
    }

    fun getParser(input: String): SMVParser {
        return SMVFacade.getParser(CharStreams.fromString(input))
    }

    @Throws(IOException::class)
    fun getParser(f: File): SMVParser {
        return SMVFacade.getParser(CharStreams.fromFileName(f.absolutePath))
    }

    fun toExpr(s: String): SMVExpr {
        val v = SMVTransformToAST()
        val e = getParser(s).expr().accept(v) as SMVExpr
        return getParser(s).expr().accept(v) as SMVExpr
    }
}
