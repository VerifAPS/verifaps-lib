/*
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

package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.STSimplifier

/**
 * Embed the GVL in the program's scope and rename the GVL variables accordingly.
 *
 * @author Augusto Modanese, Alexander Weigl
 */
class GlobalVariableListEmbedding : ST0Transformation {
    override fun transform(state: STSimplifier.State) {
        // Squash "GVL" prefix with variable name
        //state.inputElements.accept(new GVLRenameVisitor());

        // Move variable declarations to program
        state.globalVariableList.scope.forEach { v ->
            // **** Renaming disabled! ****
            //v.setName(GVL_NEW_PREFIX + v.getName());
            v.type = VariableDeclaration.GLOBAL
            state.theProgram!!.scope.add(v)
        }

        /*state.theProgram!!.scope.parent!!.forEach { v ->
            // **** Renaming disabled! ****
            //v.setName(GVL_NEW_PREFIX + v.getName());
            v.type = VariableDeclaration.GLOBAL
            state.theProgram!!.scope.add(v)
        }*/
    }

    internal class GVLRenameVisitor : AstMutableVisitor() {
        override fun visit(symbolicReference: SymbolicReference): Expression {
            if (symbolicReference.hasSub())
                symbolicReference.sub!!.accept(this)
            if (symbolicReference.identifier == GVL_NAME) {
                assert(symbolicReference.hasSub())
                symbolicReference.sub!!.identifier = GVL_NEW_PREFIX + symbolicReference.sub!!.identifier
                return symbolicReference.sub!!
            }
            return super.visit(symbolicReference)
        }
    }

    companion object {
        /**
         * Prefix to access GVL variables.
         */
        private val GVL_NAME = "GVL"

        /**
         * New prefix to rename variables with.
         */
        private val GVL_NEW_PREFIX = "GVL" + "$"
    }
}
