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
package edu.kit.iti.formal.smv.parser

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.smv.ast.SMVModule
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (10.06.17)
 */
object ModuleTests {
    @ParameterizedTest
    @MethodSource("getScripts")
    fun parse(f: File) {
        val l = SMVLexer(CharStreams.fromFileName(f!!.absolutePath))
        l.allTokens.forEach { println(it) }

        val slp = TestHelper.getParser(f!!)
        val ctx = slp.modules()

        val a = SMVTransformToAST()
        val list = ctx.accept(a) as List<SMVModule>
        for (m in list) {
            // SMVPrinter.toFile(m, File(f!!.absolutePath + ".smv"))
            System.out.println(m.toString())
        }
        Assertions.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
    }

    @JvmStatic
    fun getScripts() = TestHelper.getResourcesAsParameters("edu/kit/iti/formal/smv/parser/modules")
}
