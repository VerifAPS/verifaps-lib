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

import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.RequiredArgsConstructor;

/**
 * Conduct static analysis to find the effective subtypes of all references (including interface-type references).
 * <p>
 * Based on abstract interpretation. The abstract domains are the class and FB types in the program. Look for
 * invocations and assignments to infer possible subtypes.
 * <p>
 * Intended to be repeatedly called until a fixpoint is reached.
 * <p>
 * Usage:
 * FindEffectiveSubtypes fes = new FindEffectiveSubtypes();
 * while (!fes.fixpointReached()) {
 * fes.prepareRun();
 * ast.accept(fes);
 * }
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
public class FindEffectiveSubtypes extends AstVisitor {
    private final Scope globalScope;
    private final InstanceScope instanceScope;
    /**
     * Whether a fixpoint has been found.
     */
    private boolean fixpoint = false;
    /**
     * Keep track of current TopLevelScopeElement being visited.
     */
    private TopLevelScopeElement currentTopLevelScopeElement;

    /**
     * @return Whether we have reached a fixpoint after the last run.
     */
    public boolean fixpointReached() {
        return fixpoint;
    }

    /**
     * Prepare the next analysis run.
     */
    public void prepareRun() {
        fixpoint = true;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        visit((TopLevelScopeElement) functionDeclaration);
        return super.visit(functionDeclaration);
    }

    @Override
    public Object visit(MethodDeclaration method) {
        visit((TopLevelScopeElement) method);
        return super.visit(method);
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        visit((TopLevelScopeElement) functionBlockDeclaration);
        return super.visit(functionBlockDeclaration);
    }

    @Override
    public Object visit(ClassDeclaration clazz) {
        visit((TopLevelScopeElement) clazz);
        return super.visit(clazz);
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        visit((TopLevelScopeElement) programDeclaration);
        return super.visit(programDeclaration);
    }

    public void visit(TopLevelScopeElement topLevelScopeElement) {
        currentTopLevelScopeElement = topLevelScopeElement;
    }

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        // Base case
        if (variableDeclaration.getDataType() instanceof ClassDataType)
            variableDeclaration.addEffectiveDataType(variableDeclaration.getDataType());
            // Add all possible cases
            // TODO: rewrite
        else if (variableDeclaration.getDataType() instanceof InterfaceDataType) {
            globalScope.getClasses().stream()
                    .filter(c -> c.implementsInterface(
                            ((InterfaceDataType) variableDeclaration.getDataType()).getInterfaceDeclaration()))
                    .filter(c -> !instanceScope.getInstancesOfClass(c).isEmpty())
                    .forEach(c -> variableDeclaration.addEffectiveDataType(globalScope.resolveDataType(c.getName())));
            assert variableDeclaration.getEffectiveDataTypes().size() > 0;
        } else if (variableDeclaration.getDataType() instanceof ReferenceType) {
            ClassDeclaration clazz = ((ClassDataType) ((ReferenceType) variableDeclaration.getDataType()).getOf())
                    .getClazz();
            globalScope.getClasses().stream()
                    .filter(c -> c.equals(clazz) || c.extendsClass(clazz))
                    .filter(c -> !instanceScope.getInstancesOfClass(c).isEmpty())
                    .forEach(c -> variableDeclaration.addEffectiveDataType(globalScope.resolveDataType(c.getName())));
            assert variableDeclaration.getEffectiveDataTypes().size() > 0;
        }
        return super.visit(variableDeclaration);
    }

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        /*  TODO: rewrite
        VariableDeclaration variableDeclaration = (VariableDeclaration) resolveReference(
                (SymbolicReference) assignmentStatement.getLocation());
        // We are interested in (regular) references and interface types
        if (variableDeclaration.getDataType() instanceof AnyReference
                || variableDeclaration.getDataType() instanceof InterfaceDataType) {
            Set<Any> effectiveDataTypes = new HashSet<>();
            if (assignmentStatement.getExpression() instanceof SymbolicReference) {
                effectiveDataTypes = ((VariableDeclaration) resolveReference(
                        (SymbolicReference) assignmentStatement.getExpression())).getEffectiveDataTypes();
            }
            // TODO invocation
            for (Any dataType : effectiveDataTypes)
                if (!variableDeclaration.hasEffectiveDataType(dataType) && !(dataType instanceof InterfaceDataType)) {
                    // Register new type
                    variableDeclaration.addEffectiveDataType(dataType);
                    fixpoint = false;
                }
        }
        */
        return super.visit(assignmentStatement);
    }

    @Override
    public Object visit(Invocation invocation) {
        return super.visit(invocation);
    }

    /**
     * Resolve the type of the given expression. Assume the type can only be a class or FB data type.
     *
     * @param expression
     * @return The data type of the expression. Null if the type cannot be recognized.
     */
    private Any resolveType(Expression expression) {
        if (expression instanceof Invocation)
            return ((Invocable) resolveReference(((Invocation) expression).getCallee())).getReturnType();
        else if (expression instanceof SymbolicReference)
            return ((VariableDeclaration) resolveReference((SymbolicReference) expression)).getDataType();
        return null;
    }

    /**
     * Resolve the given reference and return the object associated with it. Used to retrieve the variable declaration
     * or the appropriate invocable from a symbolic reference.
     *
     * @param reference The symbolic reference to resolve.
     * @return The object associated with the identifier.
     */
    private Top resolveReference(SymbolicReference reference) {
        return resolveReference(reference, currentTopLevelScopeElement);
    }

    private Top resolveReference(SymbolicReference reference, TopLevelScopeElement topLevelScopeElement) {
        // Resolve the first identifier. Handle the subordinate ones recursively.
        String firstId = reference.getIdentifier();
        Top firstIdObject;
        if (firstId == "THIS")
            firstIdObject = topLevelScopeElement;
        else if (firstId == "SUPER")
            firstIdObject = ((ClassDeclaration) topLevelScopeElement).getParentClass();
        else if (topLevelScopeElement.getScope().asMap().keySet().contains(firstId)) {
            firstIdObject = topLevelScopeElement.getScope().getVariable(firstId);
            // Dereference if needed
            if (reference.getDerefCount() > 0 || reference.getSub() != null) {
                Any firstIdDataType = topLevelScopeElement.getScope().getVariable(firstId).getDataType();
                for (int i = 0; i < reference.getDerefCount(); i++)
                    firstIdDataType = ((ReferenceType) firstIdDataType).getOf();
                firstIdObject = ((RecordType) firstIdDataType).getDeclaration();
            }
        } else
            throw new DataTypeNotDefinedException("Unknown reference '" + reference + "' at " + topLevelScopeElement);
        // Recurse if needed
        if (reference.getSub() != null) {
            assert firstIdObject instanceof TopLevelScopeElement;
            return resolveReference(reference.getSub(), (TopLevelScopeElement) firstIdObject);
        }
        assert firstIdObject instanceof VariableDeclaration;
        return firstIdObject;
    }
}
