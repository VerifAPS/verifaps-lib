/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

package edu.kit.iti.formal.automation.stoo.trans;

import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.exceptions.SMVException;
import edu.kit.iti.formal.automation.oo.OOUtils;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import lombok.AllArgsConstructor;
import lombok.Getter;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Convert methods in functions. Modify the affected invocations appropriately.
 *
 * @author Augusto Modanese
 */
public class MethodToFunction extends STOOTransformation {
    private final Map<MethodDeclaration, FunctionDeclaration> newFunctions = new HashMap<>();

    @Override
    public void transform(@NotNull STOOSimplifier.State state) {
        super.transform(state);
        // Add 'self' parameter to methods
        state.getTopLevelElements().accept(new AddSelfParameterToMethodsVisitor());
        // Convert methods into functions
        state.getTopLevelElements().accept(new MethodInvocationToFunctionCallVisitor());
        state.getScope().getClasses().getAll().forEach(c -> c.getMethods().forEach(this::addNewFunction));
        state.getTopLevelElements().addAll(newFunctions.values());
        state.getTopLevelElements().accept(new RemoveMethodsVisitor());
    }

    private void addNewFunction(@NotNull MethodDeclaration method) {
        FunctionDeclaration newFunction = new FunctionDeclaration();
        newFunction.setName(((ClassDeclaration) method.getParent()).getName()
                + CLASS_METHOD_NAME_SEPARATOR + method.getName());
        newFunction.setReturnType(method.getReturnType());
        newFunction.setScope(method.getScope().copy());
        for (VariableDeclaration variable : newFunction.getScope())
            variable.setParent(newFunction);
        newFunction.setStBody(method.getStBody());
        // Possibly need to rename return variable
        newFunction.accept(new RenameReferenceVisitor(method.getName(), newFunction.getName()));
        newFunctions.put(method, newFunction);
    }

    /**
     * Remove all methods from classes.
     */
    private static class RemoveMethodsVisitor extends AstMutableVisitor {
        @Nullable
        @Override
        public Object visit(MethodDeclaration method) {
            return null;
        }
    }

    /**
     * Modify reference name.
     */
    @Getter
    @AllArgsConstructor
    private static class RenameReferenceVisitor extends AstVisitor<Object> {
        @NotNull
        private final String reference;
        @NotNull
        private final String renameTo;

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(reference)) {
                symbolicReference.setIdentifiedObject(null);
                symbolicReference.setIdentifier(renameTo);
            }
            return super.visit(symbolicReference);
        }
    }

    /**
     * Replace method invocations with function calls.
     */
    private class MethodInvocationToFunctionCallVisitor extends AstMutableVisitor {
        @NotNull
        @Override
        public Object visit(@NotNull Invocation invocation) {
            // By default don't change anything
            Invocation newInvocation = invocation;
            // Find out what we're invoking
            SymbolicReference callee = invocation.getCallee();
            // Regular function call, ignore
            if (!callee.hasSub())
                return newInvocation;
            while (callee.hasSub() && callee.getSub().hasSub())
                callee = callee.getSub();
            if (callee.getSub().getIdentifiedObject() instanceof VariableDeclaration) {
                // Invoking function block?
                VariableDeclaration variable = (VariableDeclaration) callee.getSub().getIdentifiedObject();
                if (variable.getDataType() instanceof FunctionBlockDataType
                        || state.getEffectiveSubtypeScope().getTypes(variable).stream()
                        .anyMatch(t -> t instanceof FunctionBlockDataType))
                return newInvocation;
            }
            // Callees must always be instances of classes
            assert callee.getEffectiveDataType() instanceof ClassDataType;
            ClassDeclaration calleeEffectiveClass = ((ClassDataType) callee.getEffectiveDataType()).getClazz();
            assert OOUtils.INSTANCE.hasMethod(calleeEffectiveClass, callee.getSub().getIdentifier());
            Invocable invoked = OOUtils.INSTANCE.getMethod(calleeEffectiveClass, callee.getSub().getIdentifier());
            MethodDeclaration invokedMethod = (MethodDeclaration) invoked;
            // TODO resolve THIS
            // Replace with call to function
            if (!newFunctions.containsKey(invokedMethod))
                addNewFunction(invokedMethod);
            // Function exists (if it didn't before); replace method invocation with function call
            FunctionDeclaration invokedFunction = newFunctions.get(invokedMethod);
            newInvocation = new Invocation(invokedFunction);
            newInvocation.addParameters(invocation.getParameters());
            return newInvocation;
        }
    }

    /**
     * Convert invoked instances into method parameters by passing them as 'self'.
     */
    private class AddSelfParameterToMethodsVisitor extends AstVisitor<Object> {
        /**
         * Whether we are visiting a class' method's statements.
         */
        private boolean visitingClassMethod;
        private ClassDeclaration parent;

        @Override
        public Object visit(@NotNull Invocation invocation) {
            // Pass 'self' as an additional parameter
            SymbolicReference callee = invocation.getCallee();
            if (callee.hasSub() && invocation.getParameters().stream().noneMatch(
                    p -> p.getName() != null && p.getName().equals(SELF_PARAMETER_NAME))) {
                // TODO handle THIS
                // SUPER
                if (callee.getIdentifiedObject() instanceof ClassDeclaration) {
                    SymbolicReference self = ReferenceToArrayAccess.buildGlobalArrayAccess(
                            new SymbolicReference(SELF_PARAMETER_NAME, new SymbolicReference(INSTANCE_ID_VAR_NAME)),
                            (ClassDeclaration) callee.getIdentifiedObject());
                    invocation.addParameter(new Invocation.Parameter(SELF_PARAMETER_NAME, false, self));
                }
                // Regular invocation
                else {
                    // Copy to add as SELF parameter
                    callee = callee.clone();
                    removeLastSub(callee);
                    callee.setDerefCount(0);
                    invocation.addParameter(new Invocation.Parameter(SELF_PARAMETER_NAME, false, callee));
                }
            }
            return super.visit(invocation);
        }

        @Nullable
        @Override
        public Object visit(@NotNull MethodDeclaration method) {
            HasScope parent = method.getParent();
            if (visitingClassMethod = parent instanceof ClassDeclaration) {
                this.parent = (ClassDeclaration) parent;
                visitClassMethod(method);
            }
            return null;
        }

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            // Add "self." to variables in method block which are in the instance's local scope
            if (visitingClassMethod && parent.getScope().hasVariable(symbolicReference.getIdentifier())
                    && !parent.getScope().getVariable(symbolicReference.getIdentifier()).isGlobal()
                    && !Objects.requireNonNull(parent.getScope().getVariable(symbolicReference.getIdentifier())).is(
                    VariableDeclaration.Companion.getINPUT() | VariableDeclaration.Companion.getOUTPUT() | VariableDeclaration.Companion.getINOUT()
            )) {
                symbolicReference.setSub(symbolicReference.clone());
                symbolicReference.setIdentifiedObject(null);
                symbolicReference.setIdentifier(SELF_PARAMETER_NAME);
                symbolicReference.setEffectiveDataType(state.getGlobalScope().resolveDataType(parent.getName()));
            }
            return super.visit(symbolicReference);
        }

        private void visitClassMethod(@NotNull MethodDeclaration method) {
            // Add self as VAR_IN_OUT
            if (method.getScope().hasVariable(SELF_PARAMETER_NAME))
                throw new SMVException(
                        "Method " + method + " already contains a variable named '" + SELF_PARAMETER_NAME + "'self'!");
            VariableDeclaration self = new VariableDeclaration(SELF_PARAMETER_NAME,
                    state.getScope().resolveDataType(parent.getName()));
            self.setType(VariableDeclaration.Companion.getINOUT());
            //self.setParent(method);
            method.getScope().add(self);
            // Add self access to variables in local scope which are in the class' scope
            visitingClassMethod = true;
            super.visit(method);
            visitingClassMethod = false;
        }

        /**
         * Remove the last subreference in the given reference. Does nothing in case the reference has no subreference.
         *
         * @param reference The symbolic reference to modify.
         */
        private void removeLastSub(@NotNull SymbolicReference reference) {
            if (!reference.hasSub())
                return;
            if (reference.getSub().hasSub())
                removeLastSub(reference.getSub());
            else
                reference.setSub(null);
        }
    }
}
