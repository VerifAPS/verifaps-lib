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
package edu.kit.iti.formal.automation.absint

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.st0.trans.ActionEmbedder
import edu.kit.iti.formal.automation.st0.trans.EMBEDDING_BODY_PIPELINE
import edu.kit.iti.formal.automation.st0.trans.FBEmbeddVariables
import edu.kit.iti.formal.automation.st0.trans.FBRemoveInstance
import edu.kit.iti.formal.automation.st0.trans.TimerSimplifier
import java.io.File
import java.io.PrintWriter

fun main(args: Array<String>) = AbstractIntEqSfcApp().main(args)

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.11.18)
 */
class AbstractIntEqSfcApp : CliktCommand() {
    val sfcName by option(
        "--name",
        "-n",
        metavar = "IDENTIFIER",
        help = "name of the SFC",
    )
        .default("Crane")

    val leftFile by option("--left", "-l")
        .file()
        .required()

    val rightFile by option("--right", "-r")
        .file()
        .required()

    val output: File by option("--output").file().default(File("output.dot"))

    override fun run() {
        AbstractIntEqSfc(sfcName, leftFile, rightFile, output).run()
    }
}

class AbstractIntEqSfc(
    val sfcName: String,
    val leftFile: File,
    val rightFile: File,
    val outputFile: File,
) : Runnable {
    override fun run() {
        val leftSfc = getSfc(leftFile)
        val rightSfc = getSfc(rightFile)
        val diffSfc = ConstructDifferenceSfc(leftSfc, rightSfc, true).call()

        val analyzer = AbstractInterpretationSfc(diffSfc, leftSfc.scope, rightSfc.scope)
        analyzer.run()

        outputFile.bufferedWriter().use {
            diffSfc.toDot(PrintWriter(it))
        }
        // view(diffSfc)
    }

    private fun getSfc(file: File): FunctionBlockDeclaration {
        val pous = IEC61131Facade.file(file, true)
        pous.addAll(BuiltinLoader.loadDefault())
        IEC61131Facade.resolveDataTypes(pous)

        val sfc = pous.find { it.name == sfcName }
            ?: throw IllegalArgumentException(
                "The given POU name '$sfcName' was not found in $file. " +
                    "Found: ${pous.map { it.name }}",
            )
        val network = (sfc as? PouExecutable)?.sfcBody
            ?: throw IllegalArgumentException("The given POU is not an SFC in $file.")

        val fb = sfc as? FunctionBlockDeclaration
            ?: throw IllegalArgumentException("Only Function Blocks are supported.")

        val ce =
            MultiCodeTransformation(TimerSimplifier(), ActionEmbedder(), FBEmbeddVariables(), EMBEDDING_BODY_PIPELINE)
        fb.actions.forEach { act ->
            val state = TransformationState(fb.scope, act.stBody!!)
            val nState = ce.transform(state)
            act.stBody = nState.stBody
        }
        FBRemoveInstance().transform(TransformationState(fb))
        return fb
    }
}
