package edu.kit.iti.formal.automation.sfclang

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation
import edu.kit.iti.formal.automation.sfclang.ast.SFCNetwork
import edu.kit.iti.formal.automation.sfclang.ast.SFCStep
import edu.kit.iti.formal.automation.sfclang.ast.SFCTransition
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.st.util.CodeWriter

/**
 *
 * DotPrinter class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class DotPrinter : AstVisitor<Void>() {
    private val cw = CodeWriter()

    override fun visit(decl: SFCImplementation): Void? {
        cw.append("digraph g {").increaseIndent()
        cw.nl()
        decl.networks.forEach { n -> visit(n) }
        cw.decreaseIndent()
        cw.nl().append("}")
        return null
    }

    override fun visit(n: SFCNetwork): Void? {
        cw.append("digraph f {").increaseIndent()
        cw.nl()
        n.steps.forEach { s -> s.accept(this) }
        cw.decreaseIndent()
        cw.nl().append("}")
        return null
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(decl: SFCStep): Void? {
        cw.nl().append(decl.name)
        cw.append(" [label=\"" + decl.name + "\", shape=rectangle]")
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(decl: SFCTransition): Void? {
        for (from in decl.from!!) {
            for (to in decl.to!!)
                cw.nl().append(from).append(" -> ").append(to).append(";")
        }
        return null
    }

    companion object {

        fun dot(decl: SFCImplementation): String {
            val p = DotPrinter()
            p.visit(decl)
            return p.cw.toString()
        }
    }

}
