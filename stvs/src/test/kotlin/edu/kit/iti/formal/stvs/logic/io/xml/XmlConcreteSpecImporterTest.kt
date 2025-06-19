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

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecificationTest
import edu.kit.iti.formal.stvs.model.table.JsonTableParser
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlConcreteSpecImporterTest {
    private var importer = XmlConcreteSpecImporter(listOf(TypeInt, TypeBool))

    @Test
    @Throws(Exception::class)
    fun testDoImportValid1() {
        val importedSpec = importer.doImport(javaClass.getResourceAsStream("spec_concrete_valid_1.xml")!!)
        val json = JsonTableParser.jsonFromResource("concrete_spec.json", ConcreteSpecificationTest::class.java)
        val concreteSpec = JsonTableParser.concreteTableFromJson(emptyList(), false, json)
        Assertions.assertEquals(concreteSpec, importedSpec)
    }

    @Test
    @Throws(ImportException::class)
    fun testDoImportEmpty() {
        val importedSpec: ConcreteSpecification =
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_empty.xml")!!)
        Assertions.assertEquals(ConcreteSpecification(false), importedSpec)
    }

    @Test // (expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidXml() {
        assertFailsWith<ImportException> {
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_invalid_xml_1.xml")!!)
        }
    }

    @Test // (expected = ImportException::class)
    @Throws(ImportException::class)
    fun testDoImportInvalidData() {
        assertFailsWith<ImportException> {
            importer.doImport(javaClass.getResourceAsStream("spec_concrete_invalid_data_1.xml")!!)
        }
    }
}