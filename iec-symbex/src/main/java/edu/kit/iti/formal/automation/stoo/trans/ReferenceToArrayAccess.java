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

package edu.kit.iti.formal.automation.stoo.trans;

import com.google.common.collect.Streams;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.Optional;

/**
 * Replace instances and references with INT type references. Replace accesses with these references with global array
 * accesses.
 * Depends on all symbolic references having a single effective type. This is handled by the previous transformations.
 *
 * @author Augusto Modanese
 */
public class ReferenceToArrayAccess extends STOOTransformation {
    @Override
    public void transform(@NotNull STOOSimplifier.State state) {
        super.transform(state);
        state.getTopLevelElements().accept(new ReferenceToIntVisitor());
        state.getTopLevelElements().accept(new ReferenceToArrayAccessVisitor());
    }

    static SymbolicReference buildGlobalArrayAccess(SymbolicReference index, ClassDeclaration instanceClass) {
        SymbolicReference arrayAccess = new SymbolicReference();
        arrayAccess.setIdentifier(GVL_NAME);
        arrayAccess.setSub(new SymbolicReference());
        arrayAccess.getSub().setIdentifier(INSTANCE_ARRAY_NAME_PREFIX + instanceClass.getName());
        arrayAccess.getSub().addSubscript(index);
        return arrayAccess;
    }

    /**
     * Convert a reference access to an access in the appropriate global array.
     */
    private class ReferenceToArrayAccessVisitor extends AstMutableVisitor {
        @NotNull
        @Override
        public Object visit(@NotNull SymbolicReference node) {
            // Rewrite so accesses to an instance's attributes is replaced with accesses in the appropriate global array
            List<SymbolicReference> symbolicReferenceList = node.asList();
            // Clear dereferences
            for (SymbolicReference symbolicReference : symbolicReferenceList)
                symbolicReference.setDerefCount(0);
            // Find the last instance reference, if it exists
            Optional<SymbolicReference> instanceReference = Streams.findLast(symbolicReferenceList.stream()
                    .filter(r -> r.getEffectiveDataType() instanceof ClassDataType));
            // Keep node the same in case no instance references appear
            if (!instanceReference.isPresent())
                return node;
            // Replace the reference with an array access
            // That is, if y is the instance reference: x.y.z -> GVL._INSTANCES_<class name>[x.y].z
            // TODO use buildGlobalArrayAccess (see above)
            SymbolicReference newNode = new SymbolicReference();
            newNode.setIdentifier(GVL_NAME);
            newNode.setSub(new SymbolicReference());
            // Requirement: we have a single effective type at this point
            newNode.getSub().setIdentifier(INSTANCE_ARRAY_NAME_PREFIX +
                    instanceReference.get().getEffectiveDataType().getName());
            // Take care of the instance reference's subreference (z in our example above)
            newNode.getSub().setSub(instanceReference.get().getSub());
            instanceReference.get().setSub(null);
            // Clear effective types since we took care of the instance reference
            instanceReference.get().setEffectiveDataType(null);
            // Recurse
            newNode.getSub().addSubscript((SymbolicReference) node.accept(this));
            return newNode;
        }
    }

    /**
     * Convert reference variables to INT variables. Replace REF(.) calls with the appropriate instance IDs.
     */
    private class ReferenceToIntVisitor extends AstMutableVisitor {
        @Override
        public Object visit(@NotNull Invocation invocation) {
            // Replace REF(.) with its parameter
            if (invocation.getCalleeName().equals("REF")) {
                Optional<Invocation.Parameter> o = invocation.getParameters().stream().findAny();
                assert o.isPresent();
                return o.get().getExpression().accept(this);
            }
            return super.visit(invocation);
        }

        @Override
        public Object visit(@NotNull VariableDeclaration variableDeclaration) {
            // Make sure to ignore array types; they have the same type as the array entries have
            if ((variableDeclaration.getDataType() instanceof InterfaceDataType
                    || variableDeclaration.getDataType() instanceof ReferenceType
                    || variableDeclaration.getDataType() instanceof ClassDataType)
                    && !(variableDeclaration.getTypeDeclaration() instanceof ArrayTypeDeclaration)
                    && !(variableDeclaration.isInput() || variableDeclaration.isOutput()
                        || variableDeclaration.isInOut())) {
                // Convert reference to INT reference, i.e., address in the respective array
                variableDeclaration.setTypeDeclaration(new SimpleTypeDeclaration<>());
                variableDeclaration.setDataType(
                        state.getGlobalScope().resolveDataType(INSTANCE_ID_VAR_NAME + INSTANCE_ID_TYPE_SUFFIX));
                variableDeclaration.getTypeDeclaration().setBaseType(variableDeclaration.getDataType());
                variableDeclaration.getTypeDeclaration().setBaseTypeName(variableDeclaration.getDataTypeName());
                // For top level instances (e.g., in GVL or in a program) there is a single instance for the variable,
                // so set it. For the other instances, the default is to initialize them to NULL.
                if (variableDeclaration.getInstances().size() == 1) {
                    Optional<InstanceScope.Instance> o = variableDeclaration.getInstances().stream().findAny();
                    assert o.isPresent();
                    variableDeclaration.setInit(new Literal(variableDeclaration.getDataType(),
                            Integer.toString(state.getInstanceID(o.get()))));
                } else variableDeclaration.setInit(new Literal(variableDeclaration.getDataType(),
                        Integer.toString(NULL_REFERENCE_ID)));
            }
            return super.visit(variableDeclaration);
        }

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            // Replace access to instance ID with variable itself
            if (symbolicReference.hasSub() && symbolicReference.getSub().getIdentifier().equals(INSTANCE_ID_VAR_NAME)) {
                symbolicReference.setSub(null);
                symbolicReference.setDerefCount(0);
                symbolicReference.setEffectiveDataType(null);
                return symbolicReference;
            }
            return super.visit(symbolicReference);
        }
    }
}
