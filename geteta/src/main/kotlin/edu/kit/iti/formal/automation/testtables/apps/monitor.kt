package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand

/**
 *
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */

object Monitor {
    @JvmStatic
    fun main(args: Array<String>) = MonitorApp().main(args)
}

class MonitorApp : CliktCommand() {
    override fun run() {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

}