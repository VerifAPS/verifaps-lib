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
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (12.11.19)
 */
internal class UnfoldStateTest {
    @Test
    fun testArrayRecordInit() {
        val res = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/ai_complex1_test.st")!!
        val pous = IEC61131Facade.fileResolve(CharStreams.fromStream(res))
        Assertions.assertEquals(0, pous.second.size)
        Assertions.assertEquals(6, pous.first.size)
        val us = UnfoldState()
        us.addPous(pous.first)
        val state = us.state

        for ((k, v) in state) {
            println("$k = $v")
        }

        for ((k, v) in us.decls) {
            println("$k = $v")
        }

        us.classInstances()
    }
}