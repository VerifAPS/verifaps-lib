package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.12.18)
 */
object Api {
    @JvmStatic
    fun main(args: Array<String>) {
        ApiApp().main(args)
    }
}

class ApiApp : CliktCommand(name = "ttapi") {
    val apps = HashMap<String, CliktCommand>()
    val reader = System.`in`.bufferedReader()
    val writer = System.`out`.bufferedWriter()

    override fun run() {
        do {
            val line= reader.readLine().split("[ \t]")
            val cmd = line[0]
            val args = line.drop(1)
            when (line[0]) {
                "cliFormat" -> PrinterApp().main(args)
                "gtt" -> GetetaApp().main(args)
            }
        } while (true)
    }
}

