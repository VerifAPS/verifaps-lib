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

import edu.kit.iti.formal.automation.testtables.GetetaApp
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
@RunWith(Parameterized::class)
class FullStackTest(
        var workingDir: String,
        var args: Array<String>,
        var status: String) {
    @Test
    @Throws(IOException::class, InterruptedException::class)
    fun testExtern() {
        val javaHome = System.getProperty("java.home")
        val javaBin = javaHome +
                File.separator + "bin" +
                File.separator + "java"
        val classpath = System.getProperty("java.class.path")
        val className = GetetaApp::class.java.canonicalName


        val commands = ArrayList<String>()
        commands.add(javaBin)
        commands.add("-cp")
        commands.add(classpath)
        commands.add(className)
        commands.addAll(Arrays.asList(*args))

        println(commands.stream().reduce { a, b -> "$a $b" }.get())

        val builder = ProcessBuilder(commands)
                .directory(File(workingDir).absoluteFile)
        builder.environment()["NUXMV"] = NUXMV
        val process = builder.start()
        process.waitFor()

        val output = process.inputStream.bufferedReader().useLines { it.joinToString() }
        println(output)

        process.errorStream.copyTo(System.err)

        Assert.assertEquals(0, process.exitValue().toLong())
        val lines = output.split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
        Assert.assertEquals("STATUS: " + status, lines[lines.size - 1])
    }

    companion object {
        private val CASES = ArrayList<Array<Any>>()
        var NUXMV: String

        init {
            addCase("examples/constantprogram", "verified",
                    "-t constantprogram.xml -c constantprogram.st")

            addCase("examples/constantprogram", "not-verified",
                    "-t constantprogram_broken.xml -c constantprogram.st")

            addCase("examples/constantprogram", "not-verified",
                    "-t constantprogram_concrete.xml -c constantprogram.st")

            addCase("examples/cycles", "verified",
                    "-t cycles.xml -c cycles.st")

            addCase("examples/cycles", "not-verified",
                    "-t cycles_wrong.xml -c cycles.st")




            NUXMV = (System.getenv() as java.util.Map<String, String>).getOrDefault("NUXMV", "nuXmv")
        }

        private fun addCase(wd: String, status: String, args: String) {
            CASES.add(arrayOf(wd, args.split(" ".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray(), status))
        }

        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun args(): Collection<Array<Any>> {
            return CASES
        }
    }
}
