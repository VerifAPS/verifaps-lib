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
package edu.kit.iti.formal.automation

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.19)
 */
class XPpuTest {
    @TestFactory
    fun createPPUScenarios(): List<DynamicTest> = File("../share/xPPU/")
        .listFiles { dir, name -> name.endsWith("xml") }
        .map {
            DynamicTest.dynamicTest(it.name) {
                runPPU(it)
            }
        }

    private fun runPPU(it: File) {
        println(it)
        val elements = IEC61131Facade.file(it, true)
    }
}