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
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

object ExampleParsable {
    @ParameterizedTest
    @MethodSource("findExamples")
    fun parsable(file: File) {
        val p = GetetaFacade.createParser(CharStreams.fromFileName(file.absolutePath))
        p.errorReporter.throwException()
    }

    @ParameterizedTest
    @MethodSource("findExamples")
    fun loadable(file: File) {
        GetetaFacade.parseTableDSL(file)
    }

    @JvmStatic
    fun findExamples(): List<File> {
        val walker = File("examples").walkTopDown()
        return walker.filter {
            it.isFile && (it.name.endsWith(".tt.txt") || it.name.endsWith(".gtt") || it.name.endsWith(".rtt"))
        }.toList()
    }
}
