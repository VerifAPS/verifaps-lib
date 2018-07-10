package edu.kit.iti.formal.automation

import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.07.18)
 */
object KastelDemonstrator {
    val INPUT_FILE = "/home/weigl/Documents/Kastel/Industry4.0/Demonstrator2018/code.st"

    @JvmStatic
    fun main(args: Array<String>) {
        val (pous, errors) = IEC61131Facade.filer(File(INPUT_FILE))
        errors.forEach {
            println("${it.sourceName}:${it.lineNumber} :: ${it.message} (${it.category}) ")
        }

    }
}