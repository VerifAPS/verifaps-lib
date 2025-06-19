/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main

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
            val line = reader.readLine().split("[ \t]")
            val cmd = line[0]
            val args = line.drop(1)
            when (line[0]) {
                "cliFormat" -> PrinterApp().main(args)
                "gtt" -> GetetaApp().main(args)
            }
        } while (true)
    }
}
