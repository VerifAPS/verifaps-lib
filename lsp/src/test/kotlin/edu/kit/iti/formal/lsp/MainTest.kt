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
package edu.kit.iti.formal.lsp

import edu.kit.iti.formal.lsp.gtt.GttLanguageServer
import edu.kit.iti.formal.lsp.smv.SmvLanguageServer
import edu.kit.iti.formal.lsp.st.StructuredTextLanguageServer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class MainTest {
    @Test
    fun `createLanguageServer returns the server for each language`() {
        assertTrue(createLanguageServer(Language.STRUCTURED_TEXT) is StructuredTextLanguageServer)
        assertTrue(createLanguageServer(Language.SMV) is SmvLanguageServer)
        assertTrue(createLanguageServer(Language.GTT) is GttLanguageServer)
    }

    @Test
    fun `parseLanguage accepts the documented values`() {
        assertEquals(Language.STRUCTURED_TEXT, parseLanguage("st"))
        assertEquals(Language.GTT, parseLanguage("gtt"))
        assertEquals(Language.SMV, parseLanguage("smv"))
        assertThrows(IllegalArgumentException::class.java) { parseLanguage("nope") }
    }
}