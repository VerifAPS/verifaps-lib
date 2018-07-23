package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.visitors.Utils
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.07.18)
 */
object KastelDemonstrator {
    val FOLDER = File("/home/weigl/Documents/Kastel/Industry4.0/Demonstrator2018")
    val INPUT_FILE = File(FOLDER, "VerificationSubject.st")

    @JvmStatic
    fun main(args: Array<String>) {
        val (pous, errors) = IEC61131Facade.filer(INPUT_FILE)
        errors.forEach {
            println("${it.sourceName}:${it.lineNumber} :: ${it.message} (${it.category}) ")
        }

        val program = Utils.findProgram(pous)!!
        val simplified = SymbExFacade.simplify(program)

        File(FOLDER, "Simplified.st").bufferedWriter().use {
            IEC61131Facade.printTo(it, simplified, true)
        }

    }
}