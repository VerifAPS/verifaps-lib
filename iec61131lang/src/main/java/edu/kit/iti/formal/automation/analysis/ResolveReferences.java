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
import edu.kit.iti.formal.automation.oo.OOUtils;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.RequiredArgsConstructor;

/**
 * Set identified object and its data type for every symbolic reference in code.
 *
 * @author Augusto Modanese
 */
@Data
@EqualsAndHashCode
@RequiredArgsConstructor
public class ResolveReferences extends AstVisitor<Object> {
    private final Scope globalScope;

    @Override
    public Object visit(SymbolicReference ref) {
        if (currentTopLevelScopeElement != null)
            try {
                // type of the referenced object
                AnyDt identifiedObjectDataType = null;
                // Next scope to visit
                Scope nextScope = null;
                // Next TopLevelScopeElement to visit
                TopLevelScopeElement nextTopLevelScopeElement = null;

                // THIS
                if (ref.getIdentifier().equals("THIS")) {
                    ref.setIdentifiedObject(currentTopLevelScopeElement);
                    identifiedObjectDataType = globalScope.resolveDataType(currentTopLevelScopeElement.getIdentifier());
                    nextScope = currentFullScope;
                    nextTopLevelScopeElement = currentTopLevelScopeElement;
                }
                // Variable in scope
                else if (currentFullScope.hasVariable(ref.getIdentifier())) {
                    VariableDeclaration refVariable;
                    refVariable = currentFullScope.getVariable(ref.getIdentifier());
                    ref.setIdentifiedObject(refVariable);
                    identifiedObjectDataType = refVariable.getDataType();
                    for (int i = 0; i < ref.getDerefCount(); i++)
                        identifiedObjectDataType = ((ReferenceType) identifiedObjectDataType).getOf();
                    // Array access yields array field type
                    if (identifiedObjectDataType instanceof IECArray && ref.getSubscripts() != null)
                        identifiedObjectDataType = ((IECArray) identifiedObjectDataType).getFieldType();
                    if (ref.hasSub())
                        if (identifiedObjectDataType instanceof ClassDataType) {
                            if (!(refVariable.getDataType() instanceof ReferenceType)
                                    && !(refVariable.getDataType() instanceof InterfaceDataType))
                                ref.setEffectiveDataType(refVariable.getDataType());
                            nextTopLevelScopeElement = ((ClassDataType) identifiedObjectDataType).getClazz();
                            nextScope = OOUtils.getEffectiveScope((ClassDeclaration) nextTopLevelScopeElement);
                        } else {
                            // TODO RecordType
                            // nextTopLevelScopeElement = ((RecordType) identifiedObjectDataType).getDeclaration();
                            // nextScope = nextTopLevelScopeElement.getLocalScope();
                        }
                }

                // Method
                if (currentTopLevelScopeElement instanceof ClassDeclaration
                        && OOUtils.hasMethodWithInheritance((ClassDeclaration) currentTopLevelScopeElement,
                            ref.getIdentifier())) {
                    MethodDeclaration method = OOUtils.getMethod((ClassDeclaration) currentTopLevelScopeElement,
                            ref.getIdentifier());
                    ref.setIdentifiedObject(method);
                    ref.setDataType(method.getReturnType());
                } else if (currentTopLevelScopeElement instanceof InterfaceDeclaration
                        && OOUtils.hasMethodWithInheritance((InterfaceDeclaration) currentTopLevelScopeElement,
                            ref.getIdentifier())) {
                    MethodDeclaration method = OOUtils.getMethod((InterfaceDeclaration) currentTopLevelScopeElement,
                            ref.getIdentifier());
                    ref.setIdentifiedObject(method);
                    ref.setDataType(method.getReturnType());
                }
                // SUPER (may only reference methods)
                else if (ref.getIdentifier().equals("SUPER")) {
                    ClassDeclaration parentClass = ((ClassDeclaration) currentTopLevelScopeElement).getParentClass();
                    ref.setIdentifiedObject(parentClass);
                    ref.setEffectiveDataType(globalScope.resolveDataType(parentClass.getName()));
                    if (ref.hasSub()) {
                        MethodDeclaration method = OOUtils.getMethod(parentClass, ref.getSub().getIdentifier());
                        ref.getSub().setIdentifiedObject(method);
                        ref.getSub().setDataType(method.getReturnType());
                        ref.setDataType(ref.getSub().getDataType());
                    }
                }
                // Function return value
                else if (currentTopLevelScopeElement instanceof FunctionDeclaration
                        && ref.getIdentifier().equals(((FunctionDeclaration) currentTopLevelScopeElement).getName())) {
                    ref.setIdentifiedObject(currentTopLevelScopeElement);
                    ref.setDataType(((FunctionDeclaration) currentTopLevelScopeElement).getReturnType());
                }
                // Top-level function
                else if (globalScope.getFunctions().containsKey(ref.getIdentifier())) {
                    ref.setIdentifiedObject(globalScope.getFunction(ref.getIdentifier()));
                    ref.setDataType(((FunctionDeclaration) ref.getIdentifiedObject()).getReturnType());
                } else if (ref.hasSub()) {
                    if (ref.getIdentifiedObject() instanceof VariableDeclaration
                            && identifiedObjectDataType instanceof ClassDataType
                            && OOUtils.hasMethod(((ClassDataType) identifiedObjectDataType).getClazz(),
                                ref.getSub().getIdentifier())) {
                        ref.getSub().setIdentifiedObject(
                                OOUtils.getMethod(((ClassDataType) identifiedObjectDataType).getClazz(),
                                        ref.getSub().getIdentifier()));
                        ref.getSub().setDataType(
                                ((MethodDeclaration) ref.getSub().getIdentifiedObject()).getReturnType());
                        ref.setDataType(ref.getSub().getDataType());
                    } else {
                        // Recurse
                        // Switch to local scope of top level scope element
                        Scope oldScope = currentFullScope;
                        currentFullScope = nextScope;
                        TopLevelScopeElement oldTopLevelScopeElement = currentTopLevelScopeElement;
                        currentTopLevelScopeElement = nextTopLevelScopeElement;
                        ref.getSub().accept(this);
                        ref.setDataType(ref.getSub().getDataType());
                        currentFullScope = oldScope;
                        currentTopLevelScopeElement = oldTopLevelScopeElement;
                    }
                }
                // Type value
                else if (!ref.hasSub() && currentFullScope.resolveEnum(ref.getIdentifier()) != null)
                    ref.setDataType(currentFullScope.resolveEnum(ref.getIdentifier()));
                else
                    ref.setDataType(identifiedObjectDataType);

                // Assert identified object is set for the reference
                //assert ref.getIdentifiedObject() != null;
            } catch (ClassCastException | DataTypeNotDefinedException e) {
                e.printStackTrace();
            }
        return super.visit(ref);
    }
}
