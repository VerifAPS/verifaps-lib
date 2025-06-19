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
package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.TestInstance
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (27.07.19)
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
open class TableTester {
    var gtts = ArrayList<GeneralizedTestTable>()

    @BeforeAll
    fun setUp() {
        gtts.addAll(GetetaFacade.parseTableDSL(File("src/test/resources/tables.tt")))
        Assertions.assertTrue(gtts.isNotEmpty())
    }

    fun getTable(s: String): GeneralizedTestTable {
        val t = gtts.find { it.name == s }
        Assertions.assertNotNull(t)
        t!!.ensureProgramRuns()
        t.generateSmvExpression()
        return t
    }
}