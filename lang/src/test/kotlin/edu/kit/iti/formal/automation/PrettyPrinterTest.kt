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
 * Copyright (C) 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.Top
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path
import kotlin.math.min

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
object PrettyPrinterTest {
    @Throws(IOException::class)
    fun testPrettyPrintByString(astNode: Top, file: Path) {
        val content = Files.newBufferedReader(file).readText()
        val printed = StructuredTextPrinter.print(astNode)
        Assertions.assertEquals(clean(content), clean(printed))
    }

    private fun clean(printed: String): String = printed.split("\n".toRegex())
        .dropLastWhile { it.isEmpty() }
        .map { s -> s.replace("//.*$".toRegex(), "") }
        .map { it.trim(' ', '\n') }
        .joinToString(("\n"))
        .replace("\\s+".toRegex(), " ")

    @Throws(IOException::class)
    fun testPrettyPrintByEquals(tle: PouElements) {
        val printed = IEC61131Facade.print(tle)
        IEC61131Facade.resolveDataTypes(tle)
        try {
            val newTle = IEC61131Facade.file(CharStreams.fromString(printed))
            IEC61131Facade.resolveDataTypes(newTle)
            for (i in 0 until min(tle.size, newTle.size)) {
                Assertions.assertEquals(tle[i], newTle[i])
                // Assertions.assertEquals(tle[i].toString(), newTle[i].toString())
            }
            Assertions.assertEquals(tle, newTle)
        } catch (e: SyntaxErrorReporter.ParserException) {
            System.err.println(
                e.print(printed.split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray(), "\n---\n"),
            )
            Assertions.fail("Re-parsing the printed output results into an error\n-----\n$printed")
        } finally {
            // System.err.println(printed)
        }
    }

    /*public static Stream<Object[]> files() {
        Collection<File> files = FileUtils.listFiles(new File("src/test/resources"),
                new String[]{"sfc", "st"}, true
        );
        return files.stream().map(f->new Object[]{f});
    }

    @Parameterized.Parameter
    public File toRead;
     */
}
