package edu.kit.iti.formal.automation.plcopenxml

/*-
 * #%L
 * iec-xml
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

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import org.jdom2.Element
import java.util.function.Supplier

/**
 * Construct from an &lt;interface&gt; and [edu.kit.iti.formal.automation.scope.Scope]
 *
 * @author Alexander Weigl
 * @version 1 (20.02.18)
 */
class InterfaceBuilder(val interfaze: Element) : Supplier<Scope> {
    val scope = Scope()
    override fun get(): Scope {
        val d = Scope()
        add(interfaze.getChild("inputVars"), d, VariableDeclaration.INPUT)
        add(interfaze.getChild("outputVars"), d, VariableDeclaration.OUTPUT)
        add(interfaze.getChild("localVars"), d, 0)
        //TODO Test for IN_OUT and others
        return d
    }

    protected fun add(vars: Element?, d: Scope, flags: Int) {
        if (vars == null) {
            return
        }

        for (e in vars.getChildren("variable")) {
            val name = e.getAttributeValue("name")
            val datatype = getDatatype(e.getChild("type"))
            val initValue = getInitialValue(e.getChild("initialValue"))
            val vd = VariableDeclaration(name, flags, SimpleTypeDeclaration(
                    baseType = RefTo(datatype),
                    initialization = initValue))
            scope.variables += vd
        }
    }

    protected fun getDatatype(e: org.jdom2.Element): String {
        val derived = e.getChild("derived")
        return if (derived != null) {
            derived.getAttributeValue("name")
        } else {
            e.children[0].name
        }
    }

    private fun getInitialValue(initialValue: org.jdom2.Element?): Literal? {
        if (initialValue == null) return null
        val simpleValue = initialValue.getChild("simpleValue") ?: return null
        return IEC61131Facade.expr(simpleValue.getAttributeValue("value")) as Literal
    }
}
