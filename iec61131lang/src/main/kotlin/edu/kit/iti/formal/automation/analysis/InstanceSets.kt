/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2018 Alexander Weigl
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

package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.InstanceScope
import edu.kit.iti.formal.automation.st.ast.HasScope
import edu.kit.iti.formal.automation.st.ast.Initialization
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.util.Tuple

import java.util.HashMap
import java.util.HashSet

/**
 * Map which keeps track of the (parent, variable) -> instance set mappings.
 * TODO consider namespaces
 *
 * @author Augusto Modanese
 */
class InstanceSets : HashMap<Tuple<String, String>, Set<InstanceScope.Instance>>() {
    fun addInstance(topLevelScopeElement: HasScope<*>, variable: VariableDeclaration<Initialization>,
                    instance: InstanceScope.Instance) {
        if (!containsKey(tuple(topLevelScopeElement, variable)))
            registerTuple(topLevelScopeElement, variable)
        get(tuple(topLevelScopeElement, variable)).add(instance)
    }

    fun getInstances(topLevelScopeElement: HasScope<*>,
                     variable: VariableDeclaration<Initialization>): Set<InstanceScope.Instance> {
        val instances = get(tuple(topLevelScopeElement, variable))
        if (instances == null) {
            registerTuple(topLevelScopeElement, variable)
            return get(tuple(topLevelScopeElement, variable))
        }
        return instances
    }

    private fun registerTuple(topLevelScopeElement: HasScope<*>,
                              variable: VariableDeclaration<Initialization>) {
        put(tuple(topLevelScopeElement, variable), HashSet<Instance>())
    }

    private fun tuple(topLevelScopeElement: HasScope<*>,
                      variable: VariableDeclaration<Initialization>): Tuple<String, String> {
        return Tuple(topLevelScopeElement.identifier, variable.name)
    }
}
