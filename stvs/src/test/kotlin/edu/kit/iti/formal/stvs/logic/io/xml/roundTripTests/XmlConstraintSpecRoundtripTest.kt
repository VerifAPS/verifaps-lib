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
package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecRoundtripTest {
    @ParameterizedTest
    @MethodSource("specificationFiles")
    fun constraintSpecRoundtripTest(file: File) {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(file)
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Truth.assertThat(TestUtils.removeWhitespace(fileContentsAfter)).isEqualTo(
            TestUtils.removeWhitespace(fileContentsBefore),
        )
    }

    companion object {
        @JvmStatic
        fun specificationFiles() =
            TestUtils.getTestFiles(TestUtils.FileType.CONSTRAINT, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}