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
package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class HybridRowTest {
    private var hybridRow: HybridRow? = null
    private var constraintSpec: ConstraintSpecification? = null

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        constraintSpec = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")!!,
        )
        hybridRow = HybridRow(constraintSpec!!.rows[1], constraintSpec!!.durations[1])
    }

    @Test
    @Throws(ImportException::class)
    fun testUpdateCounterExampleCells() {
        for (columnId in hybridRow!!.cells.keys) {
            val cell = hybridRow!!.cells[columnId]!!
            Assertions.assertEquals(0, cell.counterExamplesProperty.size)
        }
        Assertions.assertEquals(0, hybridRow!!.duration.counterExamplesProperty.size)
        val typeContext = listOf(TypeInt, TypeBool, enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            loadFromTestSets("/valid_1/concrete_spec_valid_1.xml")!!,
            typeContext,
        )
        hybridRow!!.updateCounterExampleCells(1, concreteSpec)
        for (columnId in hybridRow!!.cells.keys) {
            val cell = hybridRow!!.cells[columnId]!!
            Assertions.assertEquals(50, cell.counterExamplesProperty.size)
        }
        Assertions.assertEquals("50", hybridRow!!.duration.counterExamplesProperty[0])
    }
}