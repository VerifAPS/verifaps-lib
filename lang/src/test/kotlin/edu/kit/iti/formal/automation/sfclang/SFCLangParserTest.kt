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
package edu.kit.iti.formal.automation.sfclang

import LoadHelp
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.PrettyPrinterTest
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

/**
 * Created by weigl on 07.02.16.
 */
object SFCLangParserTest {

    @ParameterizedTest
    @MethodSource("getSfcs")
    fun read(inputFilename: Path) {
        val (parser, ctx) = parseSfc(inputFilename)
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
        Assertions.assertFalse(parser.errorReporter.hasErrors())
        Assertions.assertNotNull(ctx.sfcBody)
    }

    private fun parseSfc(inputFilename: Path): Pair<IEC61131Parser, FunctionBlockDeclaration> {
        val parser = IEC61131Facade.getParser(CharStreams.fromPath(inputFilename))
        val ctx = parser.function_block_declaration().accept(IECParseTreeToAST()) as FunctionBlockDeclaration
        return Pair(parser, ctx)
    }

    @ParameterizedTest
    @MethodSource("getSfcs")
    @Disabled
    fun prettyPrintByString(input: Path) {
        val (_, ctx) = parseSfc(input)
        PrettyPrinterTest.testPrettyPrintByString(ctx, input)
    }

    @JvmStatic
    fun getSfcs() = LoadHelp.getResources("/edu/kit/iti/formal/automation/sfclang/data")
}