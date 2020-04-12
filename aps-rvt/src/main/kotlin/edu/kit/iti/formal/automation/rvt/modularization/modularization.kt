package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.util.info
import kotlinx.coroutines.runBlocking

fun parseCallSitePair(it: String) = if ("=" in it) {
    val (a, b) = it.split("=")
    a to b
} else {
    it to it
}


/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
class ModularProver(val args: ModularizationApp) {
    val oldProgram = ModularProgram(args.old)
    val newProgram = ModularProgram(args.new)
    val callSitePairs: CallSiteMapping =
            args.allowedCallSites
                    .map(::parseCallSitePair)
                    .map { (a, b) ->
                        val x = oldProgram.findCallSite(a)
                                ?: error("Could not find $a")
                        val y = newProgram.findCallSite(b)
                                ?: error("Could not find $b")
                        x to y
                    }

    fun printCallSites() {
        info("Call sites for the old program: ${oldProgram.filename}")
        oldProgram.callSites.forEach {
            info("${it.repr()} in line ${it.startPosition}")
        }
        info("Call sites for the new program: ${newProgram.filename}")
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
        args.outputFolder.mkdirs()
        runBlocking(ModApp.processContext) {
            val equal = proveStrategy.equalityOf(oldProgram, newProgram)
            info("Proof result: $equal")
        }
    }
}

