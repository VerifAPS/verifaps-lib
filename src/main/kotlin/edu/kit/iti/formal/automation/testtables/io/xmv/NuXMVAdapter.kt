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
import edu.kit.iti.formal.smv.ast.SMVModule

import java.io.File
import java.io.FileWriter
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
class NuXMVAdapter(table: File, private val modules: List<SMVModule>) : Runnable {
    private val process: NuXMVProcess
    var technique: VerificationTechnique? = VerificationTechnique.IC3
        set(technique) {
            assert(technique != null)
            field = technique
        }//VerificationTechnique.INVAR;

    val isVerified: Boolean
        get() = process.isVerified

    init {
        this.process = NuXMVProcess()
                .workingDirectory(
                        File(table.parentFile,
                                table.name.replace(".xml", "")))
                .output(String.format("log_%d.txt", (Math.random() * 100).toInt()))
                .module("modules.smv")
    }

    override fun run() {
        process.workingDirectory()!!.mkdirs()
        process.commands(*this.technique!!.commands)
        try {
            createModuleFile()
        } catch (e: IOException) {
            Report.fatal("Could not create module file %s (%s)",
                    process.moduleFile(), e)
            Report.setErrorLevel("io-error")
            System.exit(1)
        }

        process.run()
    }


    @Throws(IOException::class)
    private fun createModuleFile() {
        FileWriter(process.moduleFile()!!).use { fw ->
            for (m in modules) {
                fw.write(m.toString())
                fw.write("\n")
            }
        }
    }
}
