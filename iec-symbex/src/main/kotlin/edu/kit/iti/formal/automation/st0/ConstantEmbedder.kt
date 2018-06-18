package edu.kit.iti.formal.automation.st0

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.trans.ST0Transformation

class ConstantEmbedder : ST0Transformation {
    override fun transform(state: STSimplifier.State) {
        state.functions.values.parallelStream().forEach { this.process(it) }
        process(state.theProgram!!)
    }

    private fun process(topLevelScopeElement: PouExecutable) {
        topLevelScopeElement.scope
                .forEach {
                    if (it.isConstant && it.init != null) {
                        assert(it.init is Literal)
                        topLevelScopeElement.accept(
                                ReplaceConstantVisitor(it.name, it.init as Literal))
                    }
                }
    }

    private inner class ReplaceConstantVisitor(private val constantName: String,
                                               private val constant: Literal) : AstMutableVisitor() {

        override fun visit(symbolicReference: SymbolicReference): Expression {
            if (symbolicReference.identifier == constantName) {
                assert(!symbolicReference.hasSub())
                return constant
            }
            return super.visit(symbolicReference)
        }
    }
}
