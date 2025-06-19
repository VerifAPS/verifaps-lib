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
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecificationValidatorTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.File
import java.io.FileInputStream

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporterTest {
    private var importer = XmlConstraintSpecImporter()

    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val inputStream = this.javaClass.getResourceAsStream("spec_constraint_valid_1.xml")!!
        val importedSpec: ConstraintSpecification = importer.doImport(inputStream)
        val testjson: JsonElement = JsonTableParser.jsonFromResource(
            "valid_table.json",
            ConstraintSpecificationValidatorTest::class.java,
        )

        val expectedSpec: ConstraintSpecification =
            JsonTableParser.constraintTableFromJson(testjson)
        Assertions.assertEquals(expectedSpec, importedSpec)
    }

    @Test
    @Throws(Exception::class)
    fun testDoImportValidEnum1() {
        val inputStream: FileInputStream =
            FileInputStream(File(this.javaClass.getResource("spec_constraint_valid_enum_1.xml").toURI()))
        val importedSpec: ConstraintSpecification = importer.doImport(inputStream)
        println()
    }
}