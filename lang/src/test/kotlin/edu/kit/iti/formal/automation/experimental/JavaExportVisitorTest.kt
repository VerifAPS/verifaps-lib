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
package edu.kit.iti.formal.automation.experimental

import LoadHelp
import edu.kit.iti.formal.automation.IEC61131Facade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import org.mdkt.compiler.CompilationException
import org.mdkt.compiler.InMemoryJavaCompiler

/**
 * @author Alexander Weigl
 * @version 1 (15.02.19)
 */
class JavaExportVisitorTest {
    @Test
    fun test() {
        val p = LoadHelp.getResource("/edu/kit/iti/formal/automation/ppu.xml")
        Assumptions.assumeTrue(p != null)
        val pous = IEC61131Facade.file(p!!)

        val je = JavaExportVisitor("ppu", "PPU")
        val export = je.export(pous)
        println(export)
    }

    @Test
    fun testCrane() {
        val p = LoadHelp.getResource("/edu/kit/iti/formal/automation/st/programs/Crane.st")
        Assumptions.assumeTrue(p != null)
        val pous = IEC61131Facade.file(p!!)
        IEC61131Facade.resolveDataTypes(pous)

        val je = JavaExportVisitor("crane", "PPU")
        val export = je.export(pous)
        println(export)
        Assertions.assertTrue(
            compileJava("crane", "PPU", export),
            "Could not compile source file",
        )
    }

    fun compileJava(packageName: String, className: String, content: String): Boolean {
        val packageName = packageName.replace('.', '/')
        try {
            val helloClass = InMemoryJavaCompiler.newInstance().compile(
                "$packageName.$className",
                content,
            )
            return true
        } catch (e: CompilationException) {
            e.printStackTrace()
            return false
        }
    }
}
