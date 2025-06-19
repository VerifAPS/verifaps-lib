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
package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.ParameterHolder
import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.util.currentDebugLevel
import kotlin.system.exitProcess

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/11/20)
 */
class ProgramOptions : OptionGroup("options for handling programs") {
    fun readProgram(): PouExecutable {
        val pous = IEC61131Facade.readProgramsWLPN(library, program, builtins)
        require(pous.isNotEmpty()) { "No program was given" }
        val exec = pous.first()
        require(exec != null) { "Could not find any program by ${program.first()}" }
        return exec
    }

    fun readPrograms(): List<PouExecutable> {
        val pous = IEC61131Facade.readProgramsWLPN(library, program, builtins)
        require(pous.isNotEmpty()) { "No program was given" }
        val exec = pous.first()
        require(exec != null) { "Could not find any program by ${program.first()}" }
        return pous.filterNotNull()
    }

    val builtins by option("--load-builtins", "-b", help = "Load built-ins").flag()

    val library by option("-L", "--library", help = "Library files to include in the namespace").file().multiple()

    val program by option("-P", "--program", "-c", help = "File containing the main program")
        .multiple(required = true)

    val disableSimplify by option("--no-simplify", help = "Disable the simplification to ST0")
        .flag("--simplify", default = false)
}

class CommonArguments : OptionGroup() {
    fun enableVerbosity() {
        if (verbose) {
            currentDebugLevel = 3
        }
    }

    fun showVersion() {
        if (version) {
            val urls = javaClass.classLoader.getResource("META-INF/version.property")
            urls?.openStream()?.use {
                it.transferTo(System.out)
            }
        }
        exitProcess(0)
    }

    operator fun invoke() {
        enableVerbosity()
        showVersion()
    }

    val verbose by option("--verbose", help = "enable detailed output message").flag()
    val version by option("--version", help = "show current version").flag()
}

fun ParameterHolder.nuxmv() = option(
    "--nuxmv",
    help = "Path to nuXmv binary. You can also set the environment variable \$NUXMV",
    envvar = "NUXMV",
)
    .default("nuXmv")

fun ParameterHolder.dryRun() = option("--model-check", help = "the model checker is invoked when set [default:true]")
    .flag("--dont-model-check", "--dry-run", default = true)

fun ParameterHolder.outputFolder() = option("-o", "--output", help = "Output directory")
    .default(".")
