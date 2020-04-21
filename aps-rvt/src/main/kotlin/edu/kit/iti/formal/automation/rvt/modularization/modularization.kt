package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.info
import kotlinx.coroutines.runBlocking
import java.io.File

/**
 *
 */
class ReveContext {
    fun relationOf(oldVar: String, newVar: String): SBinaryOperator =
            relation.find { it.oldVar.name == oldVar && it.newVar.name == newVar }?.operator ?: SBinaryOperator.EQUAL

    /**
     * Sub context relation, we are using an heuristic.
     */
    operator fun compareTo(c: ReveContext): Int {
        if (c.isPerfect) {
            if (isPerfect) return 0
            return -1
        }
        return 1
    }

    val isPerfect: Boolean
        get() = onlyEquivalence && condition == SLiteral.TRUE

    val condition: SMVExpr = SLiteral.TRUE
    val relation: MutableList<RelatedVariables> = arrayListOf()

    val onlyEquivalence: Boolean
        get() {
            return relation.all { it.operator == SBinaryOperator.EQUAL }
        }
}

data class RelatedVariables(
        val oldVar: SVariable,
        val operator: SBinaryOperator,
        val newVar: SVariable) {
    val expr
        get() = SBinaryExpression(oldVar, operator, newVar)
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
class ModularProver(
        val oldProgram: ModularProgram,
        val newProgram: ModularProgram,
        var context: ReveContext = ReveContext(),
        var callSitePairs: CallSiteMapping = arrayListOf(),
        var outputFolder: File = File(".")
) {

    fun printCallSites() {
        info("Call sites for the old program: ${oldProgram.entry.name}")
        oldProgram.callSites.forEach {
            info("${it.repr()} in line ${it.startPosition}")
        }
        info("Call sites for the new program: ${newProgram.entry.name}")
        newProgram.callSites.forEach {
            info("${it.repr()} in line ${it.startPosition}")
        }
    }

    fun printContexts() {
        /*args.showContexts
                .map(::parseCallSitePair)
                .map { (a, b) -> oldProgram.findCallSite(a) to newProgram.findCallSite(b) }
                .forEach { (o, n) ->
                    val keys = o.inferedContext.keys.intersect(n.inferedContext.keys)
                    val smv = keys.joinToString("&") {
                        "${o.inferedContext[it]}=${n.inferedContext[it]}"
                    }
                    println("'${o.repr()}=${n.repr()}/$smv")
                }
         */
    }

    fun proof() {
        val proveStrategy = DefaultEqualityStrategy(this)
        outputFolder.mkdirs()
        runBlocking(ModApp.processContext) {
            val equal = proveStrategy.proofEquivalenceTopLevel()
            info("Proof result: $equal")
        }
    }
}


