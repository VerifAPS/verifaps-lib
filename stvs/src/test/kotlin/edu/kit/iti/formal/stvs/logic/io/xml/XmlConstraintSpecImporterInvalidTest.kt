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
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.IOException
import java.io.InputStream
import java.net.URISyntaxException

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporterInvalidTest {
    /**
     * Test whether ConstraintSpecifications with invalid data can be imported without throwing
     * exceptions. This must be possible since the user should not be prevented from importing and
     * ConstraintSpecifications containing syntax errors and other invalid data.
     * The conformance of the result of the import with the expected result is assured in other
     * unit tests (see [XmlConstraintSpecImporterTest],
     * [edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests.XmlConstraintSpecRoundtripTest]).
     */
    @ParameterizedTest
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecImporterInvalidTest(name: String, file: InputStream) {
        ImporterFacade.importConstraintSpec(file)
    }

    companion object {
        @JvmStatic
        @Throws(URISyntaxException::class)
        fun testFiles() = (1..4).map { i ->
            Arguments.of(
                "spec_constraint_invalid_data_$i.xml",
                XmlConstraintSpecImporter::class.java.getResourceAsStream("spec_constraint_invalid_data_$i.xml"),
            )
        }
    }
}