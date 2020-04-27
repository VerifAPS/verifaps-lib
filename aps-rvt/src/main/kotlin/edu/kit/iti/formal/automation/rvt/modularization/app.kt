package edu.kit.iti.formal.automation.rvt.modularization

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.sfclang.getUniqueName
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.newFixedThreadPoolContext
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */
object ModApp {
    val processContext = newFixedThreadPoolContext(1, "aps-rvt")

    @JvmStatic
    fun main(args: Array<String>) {
        ModularizationApp().main(args)
    }
}

class ModularizationApp : CliktCommand() {
    val v by option("-v", help = "enable verbose mode").flag()
    val old by option("--old", help = "old program ").required()
    val new by option("--new", help = "new program").required()

    val showInfos by option("--info",
            help = "print contextes of call site pairs infered by symbex").flag()

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

    val inputRelation by option("-ri", "--rel-input").convert() { ModFacade.parseRelation(it) }.multiple()
    val outputRelation by option("-ro", "--rel-output").convert() { ModFacade.parseRelation(it) }.multiple()
    val condition by option("-c", "--condition").convert { SMVFacade.expr(it) }.multiple()

    val run: Boolean by option("--run", "-r", help = "run prover").flag()

    val relationalFrameContracts
            by option("-fc", "--add-frame-contract", "-s", help = "call sites to abstract")
                    .multiple()

    val outputFolder by option("-o", "--output", help = "output folder")
            .convert { File(it) }
            .default(File(getUniqueName("output_")))

    val library by option().file().multiple()

    override fun run() {
        outputFolder.mkdirs()
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
        info("Top level conditon: ${ctx.condition}")
        info("Proof for perfect equality? ${ctx.isPerfect}")
        info("Only equalities? ${ctx.onlyEquivalence}")

        val reveContextManager = ModFacade.createReveContextsBySpecification(
                relationalFrameContracts, oldProgram, newProgram)

        val m = ModularProver(
                oldProgram, newProgram,
                callSitePairs = reveContextManager.pairs,
                context = ctx,
                outputFolder = outputFolder
        )
        m.ctxManager = reveContextManager

        m.proveStrategy.disableCheckCache = disableCheckCache
        m.proveStrategy.disableProofBodyEquivalenceClassic = disableProofBodyEquivalenceClassic
        m.proveStrategy.disableProofBodyEquivalenceSMT = disableProofBodyEquivalenceSMT
        m.proveStrategy.disableProofBodyEquivalenceSSA = disableProofBodyEquivalenceSSA
        m.proveStrategy.disableProofBodyEquivalenceSource = disableProofBodyEquivalenceSource
        m.proveStrategy.disableProofBodyEquivalenceWithAbstraction = disableProofBodyEquivalenceWithAbstraction
        m.proveStrategy.disableProofBodyEquivalenceWithAbstractionBody = disableProofBodyEquivalenceWithAbstractionBody
        m.proveStrategy.disableProofBodyEquivalenceWithAbstractionSubFrames = disableProofBodyEquivalenceWithAbstractionSubFrames
        m.proveStrategy.disableUpdateCache = disableUpdateCache

        m.printCallSites()
        if (!showInfos) {
            info("Output folder: ${outputFolder}")
            info("Start with the proof")
            m.proof()
        }
    }
}
