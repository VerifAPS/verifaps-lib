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
package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.util.findProgram
import org.junit.Assume
import org.junit.jupiter.api.Test
import java.io.File

const val BASE = "src/test/resources/modularization"

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.18)
 */
class ModularizationIntegrationTest {
    @Test
    fun testProgram() {
        Assume.assumeNotNull(findProgram("nuXmv"))

        val old = File("$BASE/program1.st").absolutePath
        val new = File("$BASE/program2.st").absolutePath
        val args = arrayOf(
            "--old", old, "--new", new, "-o", "build/testProgram",
            "-s", "PGRM.INST_A.0=PGRM.INST_A.0",
            "-s", "PGRM.INST_B.0=PGRM.INST_B.0",
        )
        ModApp.main(args)
    }

    @Test
    fun testScenario() {
        val old = File("$BASE/scenario1.st").absolutePath
        val new = File("$BASE/scenario0.st").absolutePath
        val args = arrayOf(
            "--old", old, "--new", new, "-o", "build/testScenario",
            "-s", "Main.Mag.0=Main.Mag.0",
            "-s", "Main.Crane.0=Main.Crane.0",
        )
        ModApp.main(args)
    }

    @Test
    fun testSimple() {
        val input = File("$BASE/simpleA.st").absolutePath
        val args = arrayOf(
            "--old", "A@$input", "--new", "B@$input",
            "-o", "build/testScenario/simple",
            "-s", "A.f1.0=B.f1.0",
            "-s", "A.f2.0=B.f2.0",
        )
        ModApp.main(args)
    }

    @Test
    fun testComplexArithmetic() {
        Assume.assumeNotNull(findProgram("nuXmv"))
        Assume.assumeNotNull(findProgram("z3"))

        val input = File("$BASE/complex_arithmetic.st").absolutePath
        val args = arrayOf(
            "--old", "WARN_ABOVE@$input", "--new", "WARN_BELOW@$input",
            "-o", "build/testScenario/simple",
            "-s", "WARN_ABOVE.sm.0=WARN_BELOW.sm.0##",
            "-ri", "threshold=threshold&sensor=sensor",
            "-ro", "critical=!critical",
        )
        ModApp.main(args)
    }

    @Test
    fun testSimpleCtx() {
        val input = File("$BASE/simpleA.st").absolutePath
        val args = arrayOf(
            "--old", "A@$input", "--new", "B@$input",
            "-o", "build/testScenario/simple",
            "-fc", "A.f1.0=B.f1.0##",
            "-fc", "A.f2.0=B.f2.0##",
            "--info",
        )
        ModApp.main(args)
    }
}