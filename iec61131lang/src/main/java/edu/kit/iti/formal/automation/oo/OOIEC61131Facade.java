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

package edu.kit.iti.formal.automation.oo;

import edu.kit.iti.formal.automation.analysis.FindEffectiveSubtypes;
import edu.kit.iti.formal.automation.analysis.FindInstances;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import org.jetbrains.annotations.NotNull;

/**
 * Façade for object-oriented IEC 61131-3.
 *
 * @author Augusto Modanese
 */
public class OOIEC61131Facade {
    private static final int FIND_EFFECTIVE_SUBTYPES_LIMIT = 10;

    /**
     * Find all instances of classes and FBs belonging to the given top level element..
     * @param element The top level element to visit.
     * @param globalScope Global scope after data types have been resolved.
     * @return The instance scope containing all instances.
     */
    public static InstanceScope findInstances(@NotNull TopLevelElement element, @NotNull Scope globalScope) {
        InstanceScope instanceScope = new InstanceScope(globalScope);
        element.accept(new FindInstances(instanceScope));
        return instanceScope;
    }

    public static EffectiveSubtypeScope findEffectiveSubtypes(TopLevelElements topLevelElements,
                                                              Scope globalScope, InstanceScope instanceScope) {
        FindEffectiveSubtypes findEffectiveSubtypes = new FindEffectiveSubtypes(globalScope, instanceScope);
        int i;
        for (i = 0; i < FIND_EFFECTIVE_SUBTYPES_LIMIT && !findEffectiveSubtypes.fixpointReached(); i++) {
            findEffectiveSubtypes.prepareRun();
            topLevelElements.accept(findEffectiveSubtypes);
        }
        //System.out.println("Done: fixpoint is " + findEffectiveSubtypes.fixpointReached() + " after " + i + " steps");
        return findEffectiveSubtypes.getEffectiveSubtypeScope();
    }
}
