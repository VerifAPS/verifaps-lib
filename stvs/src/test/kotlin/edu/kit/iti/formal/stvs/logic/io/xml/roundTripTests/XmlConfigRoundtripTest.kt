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
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

/**
 * Created by bal on 03.03.17.
 */
class XmlConfigRoundtripTest {
    @ParameterizedTest
    @MethodSource("configFiles")
    fun configRoundtripTest(file: File) {
        val fileContentsBefore = file.reader().readText()
        val importedConfig = ImporterFacade.importConfig(file)
        val fileContentsAfter = TestUtils.stringOutputStream {
            ExporterFacade.exportConfig(importedConfig, it)
        }

        Truth.assertThat(TestUtils.removeWhitespace(fileContentsAfter))
            .isEqualTo(TestUtils.removeWhitespace(fileContentsBefore))
    }

    companion object {
        @JvmStatic
        fun configFiles(): Collection<Arguments> =
            TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}