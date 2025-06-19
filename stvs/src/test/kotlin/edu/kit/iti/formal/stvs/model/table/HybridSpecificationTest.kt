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
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class HybridSpecificationTest {
    private lateinit var hybridSpec: HybridSpecification

    @BeforeEach
    fun before() {
        hybridSpec = ImporterFacade.importHybridSpec(loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"))
    }

    private val concreteInstance = ImporterFacade.importConcreteSpec(
        loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"),
        listOf(
            TypeInt,
            TypeBool,
            TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"),
        ),
    )

    @Test
    fun counterExample() {
        Assertions.assertEquals(null, hybridSpec.counterExample)
    }

    @Test
    fun getConcreteInstance() {
        Assertions.assertEquals(null, hybridSpec.concreteInstance)
        hybridSpec.concreteInstance = concreteInstance
        Assertions.assertEquals(concreteInstance, hybridSpec.concreteInstance)
    }

    @Test
    fun getCounterExample() {
        Assertions.assertEquals(null, hybridSpec.counterExample)
        hybridSpec.counterExample = (concreteInstance)
        Assertions.assertEquals(concreteInstance, hybridSpec.counterExample)
    }

    @Test
    fun getSetSelection() {
        Assertions.assertEquals(Selection(), hybridSpec.getSelection())
        hybridSpec.getSelection().row = (3)
        hybridSpec.getSelection().column = ("A")
        Assertions.assertEquals(Selection("A", 3), hybridSpec.getSelection())
    }

    @Test // (expected = IllegalArgumentException::class)
    fun concreteInstanceInvalid() {
        val xmlFile = TestUtils.getResource("spec_concrete_empty.xml")
        assertFailsWith<IllegalArgumentException> {
            val badConcreteSpec: ConcreteSpecification = ImporterFacade.importConcreteSpec(
                xmlFile,
                listOf(TypeInt, TypeBool),
            )
            hybridSpec.concreteInstance = badConcreteSpec
        }
    }

    @Test
    fun isEditable() {
        Assertions.assertTrue(hybridSpec.isEditable)
    }

    @Test
    fun removeConcreteInstance() {
        hybridSpec.concreteInstance = (concreteInstance)
        Assertions.assertNotNull(hybridSpec.concreteInstance)
        hybridSpec.removeConcreteInstance()
        Assertions.assertNull(hybridSpec.concreteInstance)
    }

    @Test
    fun testEquals() {
        val identical: HybridSpecification = ImporterFacade.importHybridSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"),
        )
        val identicalConcrete: ConcreteSpecification = ImporterFacade.importConcreteSpec(
            loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"),
            listOf(
                TypeInt,
                TypeBool,
                TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"),
            ),
        )
        Assertions.assertEquals(hybridSpec, identical)
        hybridSpec.concreteInstance = concreteInstance
        Assertions.assertNotEquals(hybridSpec, identical)
        identical.concreteInstance = identicalConcrete
        Assertions.assertEquals(hybridSpec, identical)
        Assertions.assertNotEquals(hybridSpec, null)
        Assertions.assertEquals(hybridSpec, hybridSpec)
    }
}