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
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.Data;

/**
 * @author Augusto Modanese
 */
@Data
@Deprecated // "not well written, not comprehensible")
public class ResolveReferences extends AstVisitor {
    /*
    private final Scope globalScope;
    protected Scope currentScope;
    protected Scope currentFullScope;
    protected TopLevelScopeElement currentTopLevelScopeElement;

    @Override
    public Object visit(SymbolicReference ref) {
        // Discover the reference's identified objects and data type and set them
        if (currentTopLevelScopeElement != null)
            try {
                Any identifiedObjectDataType = null;
                Scope newScope = null;
                TopLevelScopeElement newTopLevelScopeElement = null;

                // THIS
                if (ref.getIdentifier().equals("THIS")) {
                    ref.setIdentifiedObject(currentTopLevelScopeElement);
                    identifiedObjectDataType = globalScope.resolveDataType(currentTopLevelScopeElement.getIdentifier());
                    newScope = currentFullScope;
                    newTopLevelScopeElement = currentTopLevelScopeElement;
                }
                // Variable in scope or GVL
                else if (currentFullScope.hasVariable(ref.getIdentifier()) || ref.getIdentifier().equals("GVL")) {
                    VariableDeclaration refVariable;
                    if (ref.getIdentifier().equals("GVL")) {
                        ref = ref.getSub();
                        //refVariable = currentFullScope.getGlobalVariableList().getVariable(ref);
                    } else
                        refVariable = currentFullScope.getVariable(ref);
                    //ref.setIdentifiedObject(refVariable);
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
                            newTopLevelScopeElement = ((ClassDataType) identifiedObjectDataType).getClazz();
                            newScope = ((ClassDeclaration) newTopLevelScopeElement).getEffectiveScope();
                        } else {
                            // TODO RecordType
                            // newTopLevelScopeElement = ((RecordType) identifiedObjectDataType).getDeclaration();
                            // newScope = newTopLevelScopeElement.getScope();
                        }
                }

                // Method
                if (currentTopLevelScopeElement instanceof ClassDeclaration
                        && ((ClassDeclaration) currentTopLevelScopeElement).hasMethodWithInheritance(ref.getIdentifier())) {
                    MethodDeclaration method = ((ClassDeclaration) currentTopLevelScopeElement)
                            .getMethod(ref.getIdentifier());
                    ref.setIdentifiedObject(method);
                    ref.setDataType(method.getReturnType());
                } else if (currentTopLevelScopeElement instanceof InterfaceDeclaration
                        && ((InterfaceDeclaration) currentTopLevelScopeElement).hasMethodWithInheritance(ref.getIdentifier())) {
                    MethodDeclaration method = ((InterfaceDeclaration) currentTopLevelScopeElement)
                            .getMethod(ref.getIdentifier());
                    ref.setIdentifiedObject(method);
                    ref.setDataType(method.getReturnType());
                }
                // SUPER (may only reference methods)
                else if (ref.getIdentifier().equals("SUPER")) {
                    ClassDeclaration parentClass = ((ClassDeclaration) currentTopLevelScopeElement).getParentClass();
                    ref.setIdentifiedObject(parentClass);
                    //ref.setEffectiveDataType(globalScope.resolveDataType(parentClass));
                    if (ref.hasSub()) {
                        MethodDeclaration method = parentClass.getMethod(ref.getSub().getIdentifier());
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
                            && ((ClassDataType) identifiedObjectDataType).getClazz().hasMethod(ref.getSub().getIdentifier())) {
                        ref.getSub().setIdentifiedObject(
                                ((ClassDataType) identifiedObjectDataType).getClazz().getMethod(ref.getSub().getIdentifier()));
                        ref.getSub().setDataType(((MethodDeclaration) ref.getSub().getIdentifiedObject()).getReturnType());
                        ref.setDataType(ref.getSub().getDataType());
                    } else {
                        // Recurse
                        // Switch to local scope of top level scope element
                        Scope oldScope = currentFullScope;
                        currentFullScope = newScope;
                        TopLevelScopeElement oldTopLevelScopeElement = currentTopLevelScopeElement;
                        currentTopLevelScopeElement = newTopLevelScopeElement;
                        ref.getSub().accept(this);
                        ref.setDataType(ref.getSub().getDataType());
                        currentFullScope = oldScope;
                        currentTopLevelScopeElement = oldTopLevelScopeElement;
                    }
                }
                // Type value
                else if (globalScope.getAllowedTypeValues().contains(ref.getIdentifier())) {
                    ref.setDataType(globalScope.resolveDataType(globalScope.getTypeOfValue(ref.getIdentifier())));
                } else
                    ref.setDataType(identifiedObjectDataType);

                //assert ref.getIdentifiedObject() != null;
            } catch (ClassCastException | DataTypeNotDefinedException e) {
                e.printStackTrace();
            }
        return super.visit(ref);
    }
    */
}
