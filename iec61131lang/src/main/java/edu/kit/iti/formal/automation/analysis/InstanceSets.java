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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package edu.kit.iti.formal.automation.analysis;

import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.TopLevelScopeElement;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.Tuple;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * Map which keeps track of the (parent, variable) -> instance set mappings.
 * TODO consider namespaces
 *
 * @author Augusto Modanese
 */
public class InstanceSets extends HashMap<Tuple<String, String>, Set<InstanceScope.Instance>> {
    public void addInstance(@NotNull TopLevelScopeElement topLevelScopeElement, @NotNull VariableDeclaration variable,
                            @NotNull InstanceScope.Instance instance) {
        if (!containsKey(tuple(topLevelScopeElement, variable)))
            registerTuple(topLevelScopeElement, variable);
        get(tuple(topLevelScopeElement, variable)).add(instance);
    }

    @NotNull
    public Set<InstanceScope.Instance> getInstances(@NotNull TopLevelScopeElement topLevelScopeElement,
                                                    @NotNull VariableDeclaration variable) {
        Set instances = get(tuple(topLevelScopeElement, variable));
        if (instances == null) {
            registerTuple(topLevelScopeElement, variable);
            return get(tuple(topLevelScopeElement, variable));
        }
        return instances;
    }

    private void registerTuple(@NotNull TopLevelScopeElement topLevelScopeElement,
                               @NotNull VariableDeclaration variable) {
        put(tuple(topLevelScopeElement, variable), new HashSet<>());
    }

    @NotNull
    private Tuple<String, String> tuple(@NotNull TopLevelScopeElement topLevelScopeElement,
                                        @NotNull VariableDeclaration variable) {
        return new Tuple<>(topLevelScopeElement.getIdentifier(), variable.getIdentifier());
    }
}
