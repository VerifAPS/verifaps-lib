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
import edu.kit.iti.formal.automation.testtables.report.Counterexample
import org.apache.commons.io.IOUtils

import java.io.File
import java.io.FileWriter
import java.io.IOException
import java.util.Arrays

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class NuXMVProcess : Runnable {
    private var commands: Array<String>? = null
    private var executablePath = (System.getenv() as java.util.Map<String, String>).getOrDefault("NUXMV", "nuXmv")
    private var moduleFile: File? = null
    private var workingDirectory: File? = null
    private var outputFile: File? = null
    var isVerified: Boolean = false
        private set

    //region builder

    fun output(path: String): NuXMVProcess {
        return outputFile(File(workingDirectory, path))
    }

    fun module(path: String): NuXMVProcess {
        return moduleFile(File(workingDirectory, path))
    }

    fun outputFile(): File? {
        return outputFile
    }

    fun outputFile(f: File): NuXMVProcess {
        outputFile = f
        return this
    }

    fun commands(): Array<String>? {
        return commands
    }

    fun commands(vararg commands: String): NuXMVProcess {
        this.commands = commands
        return this
    }

    fun executablePath(): String {
        return executablePath
    }

    fun executablePath(executablePath: String): NuXMVProcess {
        this.executablePath = executablePath
        return this
    }

    fun moduleFile(): File? {
        if (moduleFile == null)
            module("source.xmv")
        return moduleFile
    }

    fun moduleFile(moduleFile: File): NuXMVProcess {
        this.moduleFile = moduleFile
        return this
    }

    fun workingDirectory(): File? {
        return workingDirectory
    }

    fun workingDirectory(workingDirectory: File): NuXMVProcess {
        this.workingDirectory = workingDirectory
        return this
    }
    //endregion

    override fun run() {
        workingDirectory!!.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile()!!.absolutePath)

        try {
            createIC3CommandFile()
        } catch (e: IOException) {
            Report.error("Could not create command file: %s in %s", IC3_XMV, workingDirectory)
            Report.setErrorLevel("io-error") //TODO more detail in error level?
            return
        }


        try {
            val pb = ProcessBuilder(*commands)
                    .directory(workingDirectory)
                    .redirectOutput(outputFile!!)
                    .redirectInput(File(workingDirectory, IC3_XMV))
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
        workingDirectory()!!.mkdirs()
        val f = File(workingDirectory, IC3_XMV)
        FileWriter(f).use { fw -> IOUtils.writeLines(Arrays.asList(*commands!!), "\n", fw) }
    }

    companion object {
        val IC3_XMV = "commands.xmv"
    }

}
