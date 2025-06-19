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
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlConfigImporterTest {
    private var importer = XmlConfigImporter()

    @Test
    fun testDoImport() {
        val inputStream = XmlConfigImporter::class.java.getResourceAsStream("config_valid_nodeps.xml")!!
        val config: GlobalConfig = importer.doImport(inputStream)
        Assertions.assertEquals(100, config.verificationTimeout)
        Assertions.assertEquals(100, config.simulationTimeout)
        Assertions.assertEquals("Comic Sans", config.editorFontFamily)
        Assertions.assertEquals(12, config.editorFontSize.toLong())
    }

    @Test
    fun testDoImportDefault() {
        val inputStream =
            javaClass.getResourceAsStream("/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default.xml")!!
        val actualConfig: GlobalConfig = importer.doImport(inputStream)
        val expectedConfig = GlobalConfig()
        expectedConfig.z3Path = "[Path to Z3 Executable]"
        expectedConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        Assertions.assertEquals(expectedConfig, actualConfig)
    }

    @Test
    fun testDoImportInvalidData() {
        assertFailsWith<ImportException> {
            val inputStream = this.javaClass.getResourceAsStream("config_invalid_1.xml")!!
            importer.doImport(inputStream)
        }
    }
}