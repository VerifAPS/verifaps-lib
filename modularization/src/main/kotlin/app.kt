package edu.kit.iti.formal.automation.modularization

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.*

import edu.kit.iti.formal.automation.sfclang.getUniqueName
import edu.kit.iti.formal.util.info
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */

object ModApp {
    @JvmStatic
    fun main(args: Array<String>) {
        ModularizationApp().main(args)
    }
}


class ModularizationApp() : CliktCommand() {
    val v by option("-v", help = "enable verbose mode").flag()
    val old by option("--old", help = "old program ").required()
    val new by option("--new", help = "new program").required()
    val list: Boolean by option("--list", "-l", help = "show call sites").flag()
    val run: Boolean by option("--run", "-r", help = "run prover").flag()
    val allowedCallSites by option("-s", "--site", help = "call sites to abstract").multiple()
    val outputFolder by option("-o", "--output", help = "output folder")
            .convert { File(it) }
            .default(File(getUniqueName("output_")))


    fun readProgramsOrError() = readProgramsOrError(old) to readProgramsOrError(new)

    override fun run() {
        val m = ModularProver(this)
        if (list) {
            m.printCallSites()
        } else {
            info("Output folder: ${outputFolder}")
            m.printCallSites()
            info("Generate SMV files")
            m.prepare()
            info("Files generated")
            if (run) {
                info("Start solvers")
                m.runSolvers()
                info("Solvers ran")
            }
        }
    }
}