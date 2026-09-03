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

import org.antlr.v4.runtime.ParserRuleContext
import org.eclipse.lsp4j.FoldingRange
import java.util.*
import java.util.concurrent.CompletableFuture

/**
 * 
 * @author Alexander Weigl 
 * @version 1 (01.09.26)
 */
open class FoldingRangeHelper {
    private val rulesOfFoldingInterests = mutableMapOf<Class<*>, (ParserRuleContext) -> String?>()

    fun <T : ParserRuleContext> registerFoldingContext(ctx: Class<T>, fn: (T) -> String?) {
        rulesOfFoldingInterests[ctx] = fn as (ParserRuleContext) -> String?
    }

    inline fun <reified T : ParserRuleContext> register(noinline fn: (T) -> String?) {
        registerFoldingContext(T::class.java, fn)
    }

    fun <T : ParserRuleContext> CompletableFuture<T>.foldingRange(): CompletableFuture<List<FoldingRange>> =
        thenApplyAsync {
            val result = ArrayList<FoldingRange>(128)
            val queue = LinkedList<ParserRuleContext>()
            queue += it
            while (queue.isNotEmpty()) {
                val n = queue.pollFirst()
                if (n.start.line == n.stop.line) continue // one line ParserRuleContext, nothing to gain by folding
                rulesOfFoldingInterests[n.javaClass]?.let {
                    it(n)?.let { text ->
                        val range = FoldingRange(n.start.line, n.stop.line)
                        range.collapsedText = text
                        result.add(range)
                    }
                }
                queue.addAll(n.children.filterIsInstance<ParserRuleContext>())
            }
            result as List<FoldingRange>
        }
}