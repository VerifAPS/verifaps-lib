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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.datatypes.InterfaceDataType;
import edu.kit.iti.formal.automation.datatypes.ReferenceType;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import javafx.util.Pair;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.jetbrains.annotations.NotNull;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * Conduct static analysis to find the effective subtypes of all references (including interface-type references).
 *
 * Based on abstract interpretation. The abstract domains are the class and FB types in the program. Look for
 * invocations and assignments to infer possible subtypes.
 *
 * Intended to be repeatedly called until a fixpoint is reached.
 *
 * Usage:
 *   FindEffectiveSubtypes fes = new FindEffectiveSubtypes();
 *   while (!fes.fixpointReached()) {
 *       fes.prepareRun();
 *       ast.accept(fes);
 *   }
 *
 * @author Augusto Modanese
 */
@RequiredArgsConstructor
@Getter
public class FindEffectiveSubtypes extends AstVisitor {
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

    private final GlobalScope globalScope;
    private final InstanceScope instanceScope;
    private final EffectiveSubtypeScope effectiveSubtypeScope = new EffectiveSubtypeScope();

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        visit ((TopLevelScopeElement) functionDeclaration);
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
        if (variableDeclaration.getDataType() instanceof ClassDataType) {
            effectiveSubtypeScope.registerVariable(variableDeclaration);
            registerType(variableDeclaration, variableDeclaration.getDataType());
        }
        // Add all possible cases
        else if (containsInstance(variableDeclaration))
            effectiveSubtypeScope.registerVariable(variableDeclaration);
        return super.visit(variableDeclaration);
    }

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        VariableDeclaration variable =
                (VariableDeclaration) resolveReference((SymbolicReference) assignmentStatement.getLocation()).getKey();
        if (containsInstance(variable))
            registerTypes(variable, resolveTypes(assignmentStatement.getExpression()));
        return super.visit(assignmentStatement);
    }

    @Override
    public Object visit(Invocation invocation) {
        TopLevelScopeElement invoked = (TopLevelScopeElement) resolveReference(invocation.getCallee()).getKey();
        for (Invocation.Parameter parameter : invocation.getParameters()) {
            VariableDeclaration variable = invoked.getLocalScope().getVariable(parameter.getName());
            if (variable != null && containsInstance(variable))
                registerTypes(variable, resolveTypes(parameter.getExpression()));
        }
        return super.visit(invocation);
    }

    private boolean containsInstance(@NotNull VariableDeclaration variable) {
        return variable.getDataType() instanceof ClassDataType
                || variable.getDataType() instanceof InterfaceDataType
                || variable.getDataType() instanceof ReferenceType;
    }

    private void registerType(@NotNull VariableDeclaration variable, @NotNull Any dataType) {
        int oldDataTypeCount = effectiveSubtypeScope.getTypes(variable).size();
        effectiveSubtypeScope.registerType(variable, dataType);
        fixpoint = fixpoint && (oldDataTypeCount == effectiveSubtypeScope.getTypes(variable).size());
    }

    private void registerTypes(@NotNull VariableDeclaration variable, @NotNull Collection<Any> dataTypes) {
        int oldDataTypeCount = effectiveSubtypeScope.getTypes(variable).size();
        effectiveSubtypeScope.registerTypes(variable, dataTypes);
        fixpoint = fixpoint && (oldDataTypeCount == effectiveSubtypeScope.getTypes(variable).size());
    }

    /**
     * Resolve the type of the given expression. Assume the type can only be a class or FB data type.
     * @param expression
     * @return The data types of the expression, as a set.
     */
    @NotNull
    private Set<Any> resolveTypes(@NotNull Expression expression) {
        Set<Any> dataTypes = new HashSet<>();
        if (expression instanceof Invocation) {
            dataTypes.add(
                    ((Invocation) expression).getCalleeName().equals("REF")
                            ? ((VariableDeclaration) resolveReference(
                            (SymbolicReference) ((Invocation) expression).getParameters()
                                    .get(0).getExpression()).getKey()).getDataType()
                            : ((Invocable) resolveReference(((Invocation) expression).getCallee()).getKey())
                            .getReturnType());
        }
        else if (expression instanceof SymbolicReference) {
            VariableDeclaration variable =
                    (VariableDeclaration) resolveReference((SymbolicReference) expression).getKey();
            dataTypes.addAll(effectiveSubtypeScope.getTypes(variable));
        }
        else {
            // TODO other cases
            throw new NotImplementedException();
        }
        return dataTypes;
    }

    /**
     * Resolve the given reference and return the object associated with it. Used to retrieve the variable declaration
     * or the appropriate invocable from a symbolic reference.
     * @param reference The symbolic reference to resolve.
     * @return The object associated with the identifier, plus its parent element (null if none).
     */
    @NotNull
    private Pair<Top, TopLevelScopeElement> resolveReference(@NotNull SymbolicReference reference) {
        while (reference.hasSub())
            reference = reference.getSub();
        if (reference.getIdentifiedObject() instanceof VariableDeclaration)
            return new Pair<>((VariableDeclaration) reference.getIdentifiedObject(),
                    ((VariableDeclaration) reference.getIdentifiedObject()).getParent());
        else if (reference.getIdentifiedObject() instanceof MethodDeclaration)
            return new Pair<>((MethodDeclaration) reference.getIdentifiedObject(),
                    ((MethodDeclaration) reference.getIdentifiedObject()).getParent());
        else if (reference.getIdentifiedObject() instanceof FunctionDeclaration)
            return new Pair<>((FunctionDeclaration) reference.getIdentifiedObject(), null);
        else
            throw new DataTypeNotDefinedException(
                    "Unknown reference '" + reference + "' at " + currentTopLevelScopeElement.getIdentifier());
    }
}
