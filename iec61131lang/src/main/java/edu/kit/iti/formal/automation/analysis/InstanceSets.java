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
import javafx.util.Pair;
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
public class InstanceSets extends HashMap<Pair<String, String>, Set<InstanceScope.Instance>> {
    public void addInstance(@NotNull TopLevelScopeElement topLevelScopeElement, @NotNull VariableDeclaration variable,
                            @NotNull InstanceScope.Instance instance) {
        if (!containsKey(pair(topLevelScopeElement, variable)))
            registerPair(topLevelScopeElement, variable);
        get(pair(topLevelScopeElement, variable)).add(instance);
    }

    @NotNull
    public Set<InstanceScope.Instance> getInstances(@NotNull TopLevelScopeElement topLevelScopeElement,
                                                    @NotNull VariableDeclaration variable) {
        Set instances = get(pair(topLevelScopeElement, variable));
        if (instances == null) {
            registerPair(topLevelScopeElement, variable);
            return get(pair(topLevelScopeElement, variable));
        }
        return instances;
    }

    private void registerPair(@NotNull TopLevelScopeElement topLevelScopeElement,
                              @NotNull VariableDeclaration variable) {
        put(pair(topLevelScopeElement, variable), new HashSet<>());
    }

    @NotNull
    private Pair<String, String> pair(@NotNull TopLevelScopeElement topLevelScopeElement,
                                      @NotNull VariableDeclaration variable) {
        return new Pair<>(topLevelScopeElement.getIdentifier(), variable.getName());
    }
}
