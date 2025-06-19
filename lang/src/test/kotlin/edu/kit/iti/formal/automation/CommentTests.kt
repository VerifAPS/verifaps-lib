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

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
class CommentTests {
    @Test
    fun oneAndStuff() {
        val s = "(* aff *) dsfsaf *)"
        val l = IEC61131Lexer(CharStreams.fromString(s))
        val toks = l.allTokens
        val v = l.vocabulary
        val names = toks.map { t -> v.getSymbolicName(t.type) }

        Assertions.assertEquals(
            Arrays.asList(
                "COMMENT",
                "WS",
                "IDENTIFIER",
                "WS",
                "MULT",
                "RPAREN",
            ),
            names,
        )
        Assertions.assertEquals(6, toks.size.toLong())
    }

    @Test
    fun mlSLmix() {
        val s = "(* \n//abc *)"
        val l = IEC61131Lexer(CharStreams.fromString(s))
        val toks = l.allTokens
        val v = l.vocabulary
        val names = toks.map { t -> v.getSymbolicName(t.type) }

        Assertions.assertEquals("COMMENT", names[0])
        Assertions.assertEquals(1, toks.size.toLong())
    }
}
