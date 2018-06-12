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

package edu.kit.iti.formal.automation.oo

/*
 * Façade for object-oriented IEC 61131-3.
 *
 * @author Augusto Modanese
 *
object OOIEC61131Facade {
    private val FIND_EFFECTIVE_SUBTYPES_LIMIT = 10

    /**
     * Find all instances of classes and FBs belonging to the given top level element..
     * @param element The top level element to visit.
     * @param globalScope Global scope after data types have been resolved.
     * @return The instance scope containing all instances.
     */
    fun findInstances(element: TopLevelElement<*>, globalScope: Scope): InstanceScope {
        val instanceScope = InstanceScope(globalScope)
        element.accept(FindInstances(instanceScope))
        return instanceScope
    }

    fun findEffectiveSubtypes(topLevelElements: TopLevelElements,
                              globalScope: Scope, instanceScope: InstanceScope): EffectiveSubtypeScope {
        val findEffectiveSubtypes = FindEffectiveSubtypes(globalScope, instanceScope)
        var i: Int
        i = 0
        while (i < FIND_EFFECTIVE_SUBTYPES_LIMIT && !findEffectiveSubtypes.fixpointReached()) {
            findEffectiveSubtypes.prepareRun()
            topLevelElements.accept<Any>(findEffectiveSubtypes)
            i++
        }
        //System.out.println("Done: fixpoint is " + findEffectiveSubtypes.fixpointReached() + " after " + i + " steps");
        return findEffectiveSubtypes.effectiveSubtypeScope
    }
}
*/