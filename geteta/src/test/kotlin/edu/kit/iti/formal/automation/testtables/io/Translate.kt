package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.st.util.CodeWriter
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.print.DSLTablePrinter
import java.io.File
import java.io.PrintWriter

/**
 * Translate every gtt in xml to the new dsl format.
 *
 * @author Alexander Weigl
 * @version 1 (13.07.18)
 */
object Translate {
    @JvmStatic
    fun main(args: Array<String>) {
        val root = File("examples")
        println(root.absolutePath)
        root.walkTopDown()
                .onEnter { it.isDirectory }
                .filter { it.name.endsWith("xml") }
                .forEach {
                    try {
                        val dsl = File(it.parentFile, it.nameWithoutExtension + ".tt.txt")
                        val gtt = GetetaFacade.readTable(it.absolutePath)
                        dsl.bufferedWriter().use {
                            DSLTablePrinter(CodeWriter(it)).print(gtt)
                        }
                    }catch (e:Exception){
                        println(it.absolutePath)
                        e.printStackTrace()
                    }
                }
    }
}