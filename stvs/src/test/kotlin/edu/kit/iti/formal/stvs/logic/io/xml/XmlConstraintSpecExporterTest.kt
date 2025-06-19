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

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.IOException

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecExporterTest {
    private var exporter: XmlConstraintSpecExporter = XmlConstraintSpecExporter()

    @Test
    @Throws(ExportException::class, IOException::class)
    fun testExportValid1() {
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java,
        )

        val codeIoVariables = listOf(
            CodeIoVariable(VariableCategory.INPUT, "INT", "Counter"),
            CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "Active"),
        )

        val typeContext = listOf(TypeInt, TypeBool)
        val testSpec = JsonTableParser.constraintTableFromJson(testjson)
        val resultString = TestUtils.stringOutputStream { exporter.export(testSpec, it) }
        val expectedString = this.javaClass.getResourceAsStream("spec_constraint_valid_1.xml")!!.reader().readText()
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}