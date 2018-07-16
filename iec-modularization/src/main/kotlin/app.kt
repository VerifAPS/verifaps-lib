package edu.kit.iti.formal.automation.modularization

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.sfclang.getUniqueName
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */

class ModularizationArgs(parser: ArgParser) {
    val v by parser.flagging("enable verbose mode")
    val old by parser.storing("old program ")
    val new by parser.storing("new program")
    val list: Boolean by parser.flagging("show call sites")
    val run: Boolean by parser.flagging("run prover")
    val allowedCallSites by parser.positionalList("-x", "call sites to abstract")
    val outputFolder by parser.storing("-o", "output folder") { File(this) }
            .default(File(getUniqueName("output_")))

    fun readProgramsOrError() = readProgramsOrError(old) to readProgramsOrError(new)
}


object ModularizationApp {
    @JvmStatic
    fun main(args: Array<String>) {
        ArgParser(args).parseInto(::ModularizationArgs).run {
            main(this)
        }
    }

    @JvmStatic
    fun main(args: ModularizationArgs) {
        val m = ModularProver(args)
        if (args.list) {
            m.printCallSites()
        } else {
            Console.info("Output folder: ${args.outputFolder}")
            Console.info("Generate SMV files")
            m.createFiles()
            if (args.run) {
                m.runSolvers()
            }
        }
    }
}

