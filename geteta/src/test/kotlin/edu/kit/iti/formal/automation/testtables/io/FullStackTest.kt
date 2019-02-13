/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
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
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.apps.Geteta
import edu.kit.iti.formal.automation.testtables.apps.GetetaApp
import edu.kit.iti.formal.util.findProgram
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.io.File
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
object FullStackTest {
    private var NUXMV = (System.getenv() as Map<String, String>).getOrDefault("NUXMV", "nuXmv")

    /*var workingDir: String,
    var args: Array<String>,
    var status: String*/

    @ParameterizedTest
    @ArgumentsSource(TestArguments::class)
    fun testIntern(workingDir: String, args: Array<String>, status: String) {
        GetetaApp().main(args)
    }

    @ParameterizedTest
    @ArgumentsSource(TestArguments::class)
    fun testExtern(workingDir: String, args: Array<String>, status: String) {
        val javaHome = System.getProperty("java.home")
        val javaBin = javaHome +
                File.separator + "bin" +
                File.separator + "java"
        val classpath = System.getProperty("java.class.path")
        val className = Geteta::class.java.canonicalName


        val commands = arrayListOf(javaBin, "-cp", classpath, className)
        commands.addAll(Arrays.asList(*args))
        //println(commands.stream().reduce { a, b -> "$a $b" }.get())

        val builder = ProcessBuilder(commands)
                .directory(File(workingDir).absoluteFile)
        val nuxmv = findProgram(NUXMV)

        Assumptions.assumeTrue(nuxmv != null)

        builder.environment()["NUXMV"] = nuxmv!!.absolutePath
        val process = builder.start()
        process.waitFor()

        val output = process.inputStream.bufferedReader().useLines { it.joinToString() }
        println(output)

        process.errorStream.copyTo(System.err)

        Assertions.assertEquals(0, process.exitValue().toLong())
        println(output)
        Assertions.assertTrue(output.endsWith("STATUS: $status"))
    }


    data class TestArgument(var wd: String, var status: String, var args: Array<String>) : Arguments {
        override fun get(): Array<Any> = arrayOf(wd, args, status)
    }

    object TestArguments : ArgumentsProvider {
        private val CASES = ArrayList<TestArgument>()

        init {
            addCase("examples/constantprogram", "verified",
                    "-t", "constantprogram.xml", "-c", "constantprogram.st")

            addCase("examples/constantprogram", "not-verified",
                    "-t", "constantprogram_broken.xml", "-c", "constantprogram.st")

            addCase("examples/constantprogram", "not-verified",
                    "-t", "constantprogram_concrete.xml", "-c", "constantprogram.st")

            addCase("examples/cycles", "verified",
                    "-t", "cycles.xml", "-c", "cycles.st")

            addCase("examples/cycles", "not-verified",
                    "-t", "cycles_wrong.xml", "-c", "cycles.st")
        }

        private fun addCase(wd: String, status: String, vararg args: String) {
            CASES += TestArgument(wd, status, args as Array<String>)
        }

        override fun provideArguments(context: ExtensionContext?) = CASES.stream()
    }
}

