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
package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.common.truth.Truth
import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecExporterTest {
    private var exporter = XmlConcreteSpecExporter()

    @Test
    fun testExportConcreteValid1() {
        val json: JsonElement =
            JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val typeContext =
            listOf(TypeInt, TypeBool, TypeFactory.enumOfName("enumD", "literalOne", "literalTwo"))
        val concreteSpec =
            ImporterFacade.importConcreteSpec(loadFromTestSets("/valid_1/concrete_spec_valid_1.xml"), typeContext)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString = loadFromTestSets("/valid_1/concrete_spec_valid_1.xml").reader().readText()
        Truth.assertThat(TestUtils.removeWhitespace(result)).isEqualTo(
            TestUtils.removeWhitespace(expectedString),
        )
    }

    @Test
    fun testExportConcreteEmpty() {
        val concreteSpec = ConcreteSpecification(false)
        val result = TestUtils.stringOutputStream { exporter.export(concreteSpec, it) }
        val expectedString = this.javaClass.getResourceAsStream("spec_concrete_empty.xml")!!.reader().readText()
        Truth.assertThat(TestUtils.removeWhitespace(result)).isEqualTo(
            TestUtils.removeWhitespace(expectedString),
        )
    }
}