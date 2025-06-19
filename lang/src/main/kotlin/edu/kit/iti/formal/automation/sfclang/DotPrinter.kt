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

import edu.kit.iti.formal.automation.st.ast.SFCImplementation
import edu.kit.iti.formal.automation.st.ast.SFCNetwork
import edu.kit.iti.formal.automation.st.ast.SFCStep
import edu.kit.iti.formal.automation.st.ast.SFCTransition
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.util.CodeWriter

/**
 *
 * DotPrinter class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class DotPrinter : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}

    private val cw = CodeWriter()

    override fun visit(decl: SFCImplementation) {
        cw.printf("digraph g {").increaseIndent()
        cw.nl()
        decl.networks.forEach { n -> visit(n) }
        cw.decreaseIndent()
        cw.nl().printf("}")
    }

    override fun visit(n: SFCNetwork) {
        cw.printf("digraph f {").increaseIndent()
        cw.nl()
        n.steps.forEach { s -> s.accept(this) }
        cw.decreaseIndent()
        cw.nl().printf("}")
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(decl: SFCStep) {
        cw.nl().printf(decl.name)
        cw.printf(" [label=\"" + decl.name + "\", shape=rectangle]")
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(decl: SFCTransition) {
        for (from in decl.from!!) {
            for (to in decl.to!!) {
                cw.nl().print(from).printf(" -> ").print(to).printf(";")
            }
        }
    }

    companion object {

        fun dot(decl: SFCImplementation): String {
            val p = DotPrinter()
            p.visit(decl)
            return p.cw.toString()
        }
    }
}
