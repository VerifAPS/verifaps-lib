package edu.kit.iti.formal.automation

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.IOException
import java.util.*


@RunWith(Parameterized::class)
class StatementTest(val testFile: String) {
    @Test
    @Throws(IOException::class)
    fun testParser() {
        val parser = IEC61131Facade.getParser(CharStreams.fromFileName(testFile))
        val ctx = parser.statement_list()
        Assert.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @Test
    @Throws(IOException::class)
    fun testCopy() {
        val sl = IEC61131Facade.statements(CharStreams.fromFileName(testFile))
        Assert.assertEquals(sl, sl.clone())
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun get(): Iterable<Array<Any>> {
            val resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/statements")
            val list = ArrayList<Array<Any>>()
            for (f in resources!!) {
                list.add(arrayOf(f.absolutePath))
            }
            return list
        }
    }
}
