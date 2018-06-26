/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
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
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io.xmv


import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import org.apache.commons.io.IOUtils
import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class NuXMVProcess(var commands: Array<String>,
                   var moduleFile: File,
                   var workingDirectory: File,
                   var outputFile: File) : Runnable {
    var executablePath = System.getenv().getOrDefault("NUXMV", "nuXmv")

    var isVerified: Boolean = false
        private set

    private constructor(builder: Builder) :
            this(builder.commands, builder.moduleFile,
                    builder.workingDirectory, builder.outputFile)

    class Builder private constructor() {
        var commands: Array<String> = VerificationTechnique.IC3.commands
        var moduleFile: File = File("modules.smv")
        var workingDirectory: File = File(".")
        var outputFile: File = File("log.txt")

        constructor(init: Builder.() -> Unit) : this() {
            init()
        }

        fun commands(init: Builder.() -> Array<String>) = apply { commands = init() }
        fun wd(init: Builder.() -> File) = apply { workingDirectory = init() }
        fun module(init: Builder.() -> File) = apply { moduleFile = init() }
        fun output(init: Builder.() -> File) = apply { outputFile = init() }
        fun build() = NuXMVProcess(this)
    }

    override fun run() {
        workingDirectory.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile.absolutePath)

        try {
            createIC3CommandFile()
        } catch (e: IOException) {
            Report.error("Could not create command file: %s in %s", COMMANDS_FILE, workingDirectory)
            Report.setErrorLevel("io-error") //TODO more detail in error level?
            return
        }


        try {
            val pb = ProcessBuilder(*commands)
                    .directory(workingDirectory)
                    .redirectOutput(outputFile!!)
                    .redirectInput(File(workingDirectory, COMMANDS_FILE))
                    .redirectErrorStream(true)

            Report.info("Start '%s'", Arrays.toString(commands))
            Report.info("wd: %s", workingDirectory)
            Report.info("Result in %s", outputFile)

            val p = pb.start()

            // destroy the sub-process, if geteta is killed.
            Runtime.getRuntime().addShutdownHook(
                    Thread { if (p.isAlive) p.destroyForcibly() })
            p.waitFor()
            val parser = NuXMVOutputParser(outputFile)
            val ce = parser.run()
            isVerified = parser.invariantHolds
        } catch (e: IOException) {
            Report.error("Error in running nuxmv: %s", e.message)
            Report.error("Command line are: %s", Arrays.toString(commands))
            Report.setErrorLevel("io-error") //TODO more detail in error level?
        } catch (e: InterruptedException) {
            e.printStackTrace()
        }

    }


    @Throws(IOException::class)
    private fun createIC3CommandFile() {
        workingDirectory.mkdirs()
        val f = File(workingDirectory, COMMANDS_FILE)
        FileWriter(f).use { fw -> IOUtils.writeLines(Arrays.asList(*commands), "\n", fw) }
    }

    companion object {
        val COMMANDS_FILE = "commands.xmv"
    }
}
