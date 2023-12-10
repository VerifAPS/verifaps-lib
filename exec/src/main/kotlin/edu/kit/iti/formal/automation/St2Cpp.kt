package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade
import java.io.File
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.19)
 */
object St2Cpp : CliktCommand() {
    //val verbose by option().flag("-V", default = false)
    //val comments by option().flag("C", default = true)
    val files by argument("FILES").file(mustBeReadable = true).multiple()
    val st0 by option("-s").flag("-S", default = false)
    val builtins by option("-b").flag("-B", default = true)
    val output by option("-o").file().default(File("out.c"))

    override fun run() {
        var (pous, errors) = IEC61131Facade.filefr(files, builtins)
        if (errors.isNotEmpty()) {
            errors.forEach { System.err.println(it.toHuman()) }
        }

        if (st0) {
            pous = SymbExFacade.simplify(pous)
        }

        output.bufferedWriter().use {
            it.write("""
            // Generated ${Date()}
            #include <stdbool.h>                
            #include <stdint.h>          
                  
            """.trimIndent())
            TranslateToCppFacade.translate(it, pous)
        }
    }

}

object ST2CppApp {
    @JvmStatic
    fun main(argv: Array<String>) {
        St2Cpp.main(argv.asList())
    }
}