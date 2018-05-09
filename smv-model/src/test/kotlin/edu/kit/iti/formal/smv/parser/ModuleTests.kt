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


import edu.kit.iti.formal.smv.SMVPrinter
import edu.kit.iti.formal.smv.ast.SMVModule
import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (10.06.17)
 */
@RunWith(Parameterized::class)
class ModuleTests(val f: File) {
    @Test
    @Throws(IOException::class)
    public fun parse() {
        val l = SMVLexer(CharStreams.fromFileName(f!!.absolutePath))
        l.allTokens.forEach { println(it) }

        val slp = TestHelper.getParser(f!!)
        val ctx = slp.modules()

        val a = SMVTransformToAST()
        val list = ctx.accept(a) as List<SMVModule>
        for (m in list) {
            //SMVPrinter.toFile(m, File(f!!.absolutePath + ".smv"))
            System.out.println(m.toString())
        }
        Assert.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        @Throws(IOException::class)
        public fun getScripts() = TestHelper.getResourcesAsParameters("edu/kit/iti/formal/smv/parser/modules")
    }

}
