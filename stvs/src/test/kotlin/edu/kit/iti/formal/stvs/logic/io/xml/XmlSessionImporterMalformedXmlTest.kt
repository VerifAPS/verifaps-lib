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

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.IOException
import java.io.InputStream
import java.net.URISyntaxException
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlSessionImporterMalformedXmlTest {
    /**
     * Test whether importing malformed XML throws ImportExceptions.
     */
    @ParameterizedTest // (expected = ImportException::class)
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun sessionImporterMalformedXmlTest(name: String, file: InputStream) {
        assertFailsWith<ImportException> { ImporterFacade.importSession(file, GlobalConfig(), History()) }
    }

    companion object {
        @JvmStatic
        @Throws(URISyntaxException::class)
        fun testFiles() = (1..5).map { i ->
            Arguments.of(
                "session_invalid_xml_$i.xml",
                XmlConstraintSpecImporter::class.java.getResourceAsStream("session_invalid_xml_$i.xml"),
            )
        }
    }
}