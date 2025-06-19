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
package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Philipp Krüger
 * @author Alexander Weigl
 */
class TestEnumParse : DefaultVisitor<Void>() {
    internal var code = "TYPE\n" +
        "  MY_ENUM : (one, two, three);\n" +
        "END_TYPE\n"

    @Test
    fun testEnumMembers() {
        val toplevel = IEC61131Facade.file(CharStreams.fromString(code))
        val decls = toplevel[0] as TypeDeclarations
        val enumdecl = decls[0] as EnumerationTypeDeclaration
        assertEquals(
            Arrays.asList("one", "two", "three"),
            enumdecl.allowedValues.map { it.text!! },
        )
    }
}