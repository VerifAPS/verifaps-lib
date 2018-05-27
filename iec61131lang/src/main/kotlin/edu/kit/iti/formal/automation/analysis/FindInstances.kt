/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.ClassDataType
import edu.kit.iti.formal.automation.scope.InstanceScope
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.util.AstVisitor
import lombok.RequiredArgsConstructor

/**
 * Visitor which finds all instances of classes and FBs and adds them to the global scope.
 *
 * Intended to be called on a single top level element to find all instances which can be traced back to it:
 * InstanceScope instanceScope = new InstanceScope(globalScope);
 * topLevelElement.accept(new FindInstances(instanceScope));
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
class FindInstances : AstVisitor<*> {
    private val instanceScope: InstanceScope? = null

    /**
     * Used during traversal to know the current parent instance.
     */
    private var parentInstance: InstanceScope.Instance? = null

    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        if (variableDeclaration.isInput || variableDeclaration.isOutput || variableDeclaration.isInOut
                || currentTopLevelScopeElement is InterfaceDeclaration)
            return super.visit(variableDeclaration)
        val dataType = variableDeclaration.dataType as? ClassDataType ?: return super.visit(variableDeclaration)
        // Only classes have instances
        val currentInstance = InstanceScope.Instance(parentInstance, variableDeclaration)
        val classDeclaration = dataType.clazz
        instanceScope!!.registerClassInstance(variableDeclaration, classDeclaration, currentInstance)
        recurse(classDeclaration, currentInstance)
        return super.visit(variableDeclaration)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        // When visiting a class, make sure to visit the variables in the parent classes too
        if (clazz.parentClass != null)
            clazz.parentClass!!.scope.accept<Any>(this)
        return super.visit(clazz)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        //TODO return super.visit((ClassDeclaration) functionBlockDeclaration);
        return null
    }

    /**
     * Recurse one level down a class or function block.
     * @param classDeclaration The class or function block to visit.
     * @param currentInstance The instance referent to classDeclaration.
     */
    private fun recurse(classDeclaration: ClassDeclaration, currentInstance: InstanceScope.Instance) {
        // Save old instance
        val oldParentInstance = parentInstance
        // Recurse
        parentInstance = currentInstance
        classDeclaration.accept<Any>(this)
        // Restore state
        parentInstance = oldParentInstance
    }
}
