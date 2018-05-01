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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package edu.kit.iti.formal.automation.analysis;

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.RequiredArgsConstructor;

/**
 * Visitor which finds all instances of classes and FBs and adds them to the global scope.
 *
 * Intended to be called on a single top level element to find all instances which can be traced back to it:
 *   InstanceScope instanceScope = new InstanceScope(globalScope);
 *   topLevelElement.accept(new FindInstances(instanceScope));
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
public class FindInstances extends AstVisitor {
    private final InstanceScope instanceScope;

    /**
     * Used during traversal to know the current parent instance.
     */
    private InstanceScope.Instance parentInstance = null;

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        if (variableDeclaration.isInput() || variableDeclaration.isOutput() || variableDeclaration.isInOut()
                || currentTopLevelScopeElement instanceof InterfaceDeclaration)
            return super.visit(variableDeclaration);
        AnyDt dataType = variableDeclaration.getDataType();
        // Only classes have instances
        if (!(dataType instanceof ClassDataType))
            return super.visit(variableDeclaration);
        InstanceScope.Instance currentInstance = new InstanceScope.Instance(parentInstance, variableDeclaration);
        ClassDeclaration classDeclaration = ((ClassDataType) dataType).getClazz();
        instanceScope.registerClassInstance(variableDeclaration, classDeclaration, currentInstance);
        recurse(classDeclaration, currentInstance);
        return super.visit(variableDeclaration);
    }

    @Override
    public Object visit(ClassDeclaration clazz) {
        // When visiting a class, make sure to visit the variables in the parent classes too
        if (clazz.getParentClass() != null)
            clazz.getParentClass().getScope().accept(this);
        return super.visit(clazz);
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        return super.visit((ClassDeclaration) functionBlockDeclaration);
    }

    /**
     * Recurse one level down a class or function block.
     * @param classDeclaration The class or function block to visit.
     * @param currentInstance The instance referent to classDeclaration.
     */
    private void recurse(ClassDeclaration classDeclaration, InstanceScope.Instance currentInstance) {
        // Save old instance
        InstanceScope.Instance oldParentInstance = parentInstance;
        // Recurse
        parentInstance = currentInstance;
        classDeclaration.accept(this);
        // Restore state
        parentInstance = oldParentInstance;
    }
}
