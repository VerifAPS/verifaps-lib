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
package edu.kit.iti.formal.automation.rvt.modularization

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.sfclang.*
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.info
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */
object ModApp {
    // val processContext = newFixedThreadPoolContext(1, "aps-rvt")
    @JvmStatic
    fun main(args: Array<String>) {
        ModularizationApp().main(args)
    }
}

class ModularizationApp : CliktCommand() {
    val v by option("-v", help = "enable verbose mode").flag()
    val old by option("--old", help = "old program ").required()
    val new by option("--new", help = "new program").required()

    val showInfos by option(
        "--info",
        help = "print contextes of call site pairs infered by symbex",
    ).flag()

    val assume by option().multiple()

    val disableProofBodyEquivalenceSMT by option(help = "").flag()
    val disableProofBodyEquivalenceSSA by option(help = "").flag()
    val disableProofBodyEquivalenceSource by option(help = "").flag()
    val disableProofBodyEquivalenceWithAbstractionSubFrames by option(help = "").flag()
    val disableProofBodyEquivalenceWithAbstractionBody by option(help = "").flag()
    val disableProofBodyEquivalenceWithAbstraction by option(help = "").flag()
    val disableProofBodyEquivalenceClassic by option(help = "").flag()
    val disableUpdateCache by option(help = "").flag()
    val disableCheckCache by option(help = "").flag()

    /*val contexts by option("--context",
            help = "expected equality of sub modules",
            metavar = "callsite=callsite/<smv>")
            .multiple()*/

    val inputRelation by option("-ri", "--rel-input", "--rel-in")
        .convert { ModFacade.parseRelation(it) }.multiple()
    val outputRelation by option("-ro", "--rel-output", "--rel-out")
        .convert { ModFacade.parseRelation(it) }.multiple()
    val condition by option("-c", "--condition").convert { SMVFacade.expr(it) }.multiple()

    val run: Boolean by option("--run", "-r", help = "run prover").flag()

    val relationalFrameContracts
        by option("-fc", "--add-frame-contract", "-s", help = "call sites to abstract")
            .multiple()

    val outputFolder by option("-o", "--output", help = "output folder")
        .convert { File(it) }
        .default(File(getUniqueName("output_")))

    val library by option().file().multiple()

    val nuxmvPath by option("--nuxmv", envvar = "NUXMV")
        .default(nuxmvDefaultPath)

    override fun run() {
        outputFolder.mkdirs()
        nuxmvDefaultPath = nuxmvPath

        val (oldExec, newExec) = IEC61131Facade.readProgramsWLPN(library, listOf(old, new))
        require(oldExec != null) { "Could not find program in $old" }
        require(newExec != null) { "Could not find program in $new" }

        val oldProgram = ModFacade.createModularProgram(oldExec, outputFolder, "old")
        val newProgram = ModFacade.createModularProgram(newExec, outputFolder, "new")

        val ctx = TopReveContext()
        ctx.inRelation = inputRelation.toMutableList()
        ctx.outRelation = outputRelation.toMutableList()
        ctx.condition = condition.conjunction(SLiteral.TRUE)

        info("Top level relation: ${ctx.inRelation.joinToString(" & ") { it.expr.repr() }}")
        info("Top level conditon: ${ctx.condition.repr()}")
        info("Proof for perfect equality? ${ctx.isPerfect}")
        info("Only equalities? ${ctx.onlyEquivalence}")

        val reveContextManager = ModFacade.createReveContextsBySpecification(
            relationalFrameContracts,
            oldProgram,
            newProgram,
        )

        val m = ModularProver(
            oldProgram,
            newProgram,
            callSitePairs = reveContextManager.pairs,
            context = ctx,
            outputFolder = outputFolder,
        )
        m.ctxManager.addAll(reveContextManager)

        m.proveStrategy.disableCheckCache = disableCheckCache
        m.proveStrategy.disableProofBodyEquivalenceClassic = disableProofBodyEquivalenceClassic
        m.proveStrategy.disableProofBodyEquivalenceSMT = disableProofBodyEquivalenceSMT
        m.proveStrategy.disableProofBodyEquivalenceSSA = disableProofBodyEquivalenceSSA
        m.proveStrategy.disableProofBodyEquivalenceSource = disableProofBodyEquivalenceSource
        m.proveStrategy.disableProofBodyEquivalenceWithAbstraction = disableProofBodyEquivalenceWithAbstraction
        m.proveStrategy.disableProofBodyEquivalenceWithAbstractionBody = disableProofBodyEquivalenceWithAbstractionBody
        m.proveStrategy.disableProofBodyEquivalenceWithAbstractionSubFrames =
            disableProofBodyEquivalenceWithAbstractionSubFrames
        m.proveStrategy.disableUpdateCache = disableUpdateCache

        m.proveStrategy.assumeAsProven.addAll(this.assume)
        info("Following sub-calls are marked as proven by assumption: ${m.proveStrategy.assumeAsProven}")

        m.printCallSites()

        if (!showInfos) {
            info("Output folder: $outputFolder")
            info("Start with the proof")
            m.proof()
        }
    }
}