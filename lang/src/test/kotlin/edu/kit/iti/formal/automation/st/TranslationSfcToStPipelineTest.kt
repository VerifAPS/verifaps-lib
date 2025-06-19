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
package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.SFCNetwork
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (20.06.19)
 */
class TranslationSfcToStPipelineTest {
    val file = "single_sfc2st_tests.st"

    @Test
    fun simple1() {
        val (scope, network) = readSfc(file, "simple1")
        val t = TranslationSfcToStPipeline(
            network,
            name = "simple1",
            scope = scope,
            maxNeededTokens = TokenAmount.Bounded(1),
            sfcFlags = false,
        )
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simple1_reset() {
        val (scope, network) = readSfc(file, "simple1")
        val t = TranslationSfcToStPipeline(
            network,
            name = "simple1",
            scope = scope,
            maxNeededTokens = TokenAmount.Bounded(1),
            sfcFlags = true,
        )
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simpleOnlyActions() {
        val (scope, network) = readSfc(file, "simpleOnlyActions")
        val t = TranslationSfcToStPipeline(
            network,
            name = "simpleOnlyActions",
            scope = scope,
            maxNeededTokens = TokenAmount.Bounded(1),
            sfcFlags = false,
        )
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simpleOnlyActions_reset() {
        val (scope, network) = readSfc(file, "simpleOnlyActions")
        val t = TranslationSfcToStPipeline(
            network,
            name = "simpleOnlyActions",
            scope = scope,
            maxNeededTokens = TokenAmount.Bounded(1),
            sfcFlags = true,
        )
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    private fun readSfc(s: String, fbdName: String): Pair<Scope, SFCNetwork> {
        val res = javaClass.getResourceAsStream(s)
        assertNotNull(res)
        val pous = IEC61131Facade.file(res).also {
            it.addAll(BuiltinLoader.loadDefault())
            IEC61131Facade.resolveDataTypes(it)
        }
        val fbd = pous.find { it.name == fbdName } as? FunctionBlockDeclaration
        assertNotNull(fbd)
        val sfc = fbd?.sfcBody?.networks?.first()
        assertNotNull(sfc)
        return fbd?.scope!! to sfc!!
    }
}