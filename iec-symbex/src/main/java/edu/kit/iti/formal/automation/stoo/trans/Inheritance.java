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

package edu.kit.iti.formal.automation.stoo.trans;

import edu.kit.iti.formal.automation.oo.OOUtils;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import lombok.RequiredArgsConstructor;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Remove inheritance by setting effective types.
 *
 * Requires symbolic references to have their effective types set (by BranchEffectiveTypes).
 *
 * @author Augusto Modanese
 */
public class Inheritance extends STOOTransformation {
    /**
     * @param accessedVariableClass The class of the accessed variable.
     * @param accessedField The field which is accessed.
     * @return If the access is valid, the class which the accessed variable inherits the field (an attribute or a
     * method) from, and the count of hierarchy levels up until this class is reached. Otherwise, return the sentinel
     * value (null, -1).
     */
    private static Tuple<ClassDeclaration, Integer> getInheritedFrom(@NotNull ClassDeclaration accessedVariableClass,
                                                                     @NotNull String accessedField) {
        ClassDeclaration parentClass = accessedVariableClass;
        int hierarchyLevel = 0;
        while (parentClass != null) {
            if (parentClass.getScope().hasVariable(accessedField) || OOUtils.INSTANCE.hasMethod(parentClass, accessedField))
                break;
            parentClass = parentClass.getParentClass();
            hierarchyLevel++;
        }
        if (parentClass == null)
            return new Tuple<>(null, -1);
        return new Tuple<>(parentClass, hierarchyLevel);
    }

    private static Tuple<ClassDeclaration, Integer> getInheritedFrom(@NotNull ClassDeclaration accessedVariableClass,
                                                                     @NotNull SymbolicReference accessedField) {
        return getInheritedFrom(accessedVariableClass, accessedField.getIdentifier());
    }

    private static ClassDeclaration getInheritedFromClass(@NotNull ClassDeclaration accessedVariableClass,
                                                          @NotNull SymbolicReference accessedField) {
        return getInheritedFrom(accessedVariableClass, accessedField).getA();
    }

    private static ClassDeclaration getInheritedFromClass(@NotNull ClassDeclaration accessedVariableClass,
                                                          @NotNull String accessedField) {
        return getInheritedFrom(accessedVariableClass, accessedField).getA();
    }

    @Override
    public void transform(@NotNull STOOSimplifier.State state) {
        super.transform(state);
        for (ClassDeclaration classDeclaration : state.getScope().getClasses().values()) {
            if (!classDeclaration.hasParentClass())
                continue;
            // Add/fix super accesses (inside class)
            List<String> classFields = OOUtils.INSTANCE.getEffectiveScope(classDeclaration).parallelStream()
                    .filter(v -> !classDeclaration.getScope().hasVariable(v.getName()))
                    .map(VariableDeclaration::getName)
                    .collect(Collectors.toList());
            for (String field : classFields) {
                ClassDeclaration inheritedFromClass = getInheritedFromClass(classDeclaration, field);
                if (!classDeclaration.equals(inheritedFromClass))
                    classDeclaration.accept(new AddSuperAccessInsideClassVisitor(field, inheritedFromClass));
            }
            // Add effective type to super accesses (outside class)
            state.getTopLevelElements().accept(new SetSuperAccessEffectiveTypeVisitor(classDeclaration));
        }
    }

    /**
     * Set appropriate effective type when accessing fields from the super class. For example, if B inherits attribute
     * x from A, b is an instance of B, and there is an expression with "b.x", then set the effective type of b in it
     * to A (instead of B).
     */
    @RequiredArgsConstructor
    private class SetSuperAccessEffectiveTypeVisitor extends AstVisitor<Object> {
        @NotNull
        private final ClassDeclaration theClass;

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            if (((symbolicReference.getEffectiveDataType() instanceof ClassDataType
                            && ((ClassDataType) symbolicReference.getEffectiveDataType()).getClazz().equals(theClass))
                        || (symbolicReference.getIdentifiedObject() instanceof VariableDeclaration
                            && ((VariableDeclaration) symbolicReference.getIdentifiedObject())
                                    .getDataType().getName().equals(theClass.getName())))
                    && symbolicReference.hasSub()) {
                SymbolicReference accessedField = symbolicReference.getSub();
                // Find in which level in the hierarchy the access field "lives"
                ClassDeclaration inheritedFromClass = getInheritedFromClass(theClass, accessedField);
                assert inheritedFromClass != null;
                // Set new effective type (cast)
                symbolicReference.setEffectiveDataType(
                        state.getScope().resolveDataType(inheritedFromClass.getName()));
            }
            return symbolicReference.hasSub() ? visit(symbolicReference.getSub()) : super.visit(symbolicReference);
        }
    }

    @RequiredArgsConstructor
    private class AddSuperAccessInsideClassVisitor extends AstMutableVisitor {
        @NotNull
        private final String field;
        @NotNull
        private final ClassDeclaration superClass;

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(field)) {
                SymbolicReference superAccess = ReferenceToArrayAccess.buildGlobalArrayAccess(
                        new SymbolicReference(SELF_PARAMETER_NAME, new SymbolicReference(INSTANCE_ID_VAR_NAME)),
                        superClass);
                superAccess.setSub(symbolicReference);
                return superAccess;
            }
            return super.visit(symbolicReference);
        }
    }
}
