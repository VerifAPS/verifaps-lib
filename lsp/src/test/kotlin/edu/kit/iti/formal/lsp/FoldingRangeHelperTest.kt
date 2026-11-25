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

import org.antlr.v4.runtime.CommonToken
import org.antlr.v4.runtime.ParserRuleContext
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.util.concurrent.CompletableFuture

private class TestRuleContext : ParserRuleContext()

class FoldingRangeHelperTest {
    @Test
    fun `folding ranges are zero based and skip single lines`() {
        val helper = FoldingRangeHelper()
        val ctx = TestRuleContext()
        ctx.start = CommonToken(0).apply { line = 1 }
        ctx.stop = CommonToken(0).apply { line = 3 }
        helper.registerFoldingContext(TestRuleContext::class.java) { "TEST" }

        val ranges = with(helper) {
            CompletableFuture.completedFuture(ctx).foldingRange().get()
        }

        assertEquals(1, ranges.size)
        assertEquals(0, ranges.single().startLine)
        assertEquals(2, ranges.single().endLine)
    }

    @Test
    fun `single-line contexts produce no folding range`() {
        val helper = FoldingRangeHelper()
        val ctx = TestRuleContext()
        ctx.start = CommonToken(0).apply { line = 4 }
        ctx.stop = CommonToken(0).apply { line = 4 }
        helper.registerFoldingContext(TestRuleContext::class.java) { "TEST" }

        val ranges = with(helper) {
            CompletableFuture.completedFuture(ctx).foldingRange().get()
        }
        assertEquals(emptyList<Any>(), ranges)
    }
}