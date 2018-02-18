package edu.kit.iti.formal.automation.analysis;


/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.val;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * ResolveDataTypes searches and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl
 * @version 1
 * @since 25.11.16
 */
public class ResolveDataTypes extends AstVisitor<Object> {
    private final Scope globalScope;
    private Scope localScope;

    public ResolveDataTypes(Scope globalScope) {
        this.globalScope = globalScope;
    }

    private Any resolve(String name) {
        return localScope.resolveDataType(name);
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.getScope().setParent(globalScope);
        return super.visit(programDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.getScope().setParent(globalScope);
        functionDeclaration.setReturnType(
                resolve(functionDeclaration.getReturnTypeName()));
        return super.visit(functionDeclaration);
    }

    @Override
    public Object visit(MethodDeclaration methodDeclaration) {
        methodDeclaration.getScope().setParent(localScope);
        methodDeclaration.setReturnType(resolve(methodDeclaration.getReturnTypeName()));
        return super.visit(methodDeclaration);
    }

    @Override
    public Object visit(Scope localScope) {
        this.localScope = localScope;
        localScope.getVariables().values().forEach(vd -> {
            vd.setDataType(resolve(vd.getDataTypeName()));
            if(vd.getInit()!=null){
                vd.getInit().accept(this);
            }
        });
        return null;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.getScope().setParent(globalScope);
        return super.visit(functionBlockDeclaration);
    }

    public <T extends ParserRuleContext> void visitClassifier(Classifier<T> c) {
        val seq = c.getInterfaces();
        seq.forEach(face ->
                face.setIdentifiedObject(c.getScope().resolveInterface(face.getIdentifier())));
    }

    @Override
    public Object visit(ClassDeclaration classDeclaration) {
        if (classDeclaration.getParentName() != null) {
            classDeclaration.getParent().setIdentifiedObject(
                    classDeclaration.getScope().resolveClass(classDeclaration.getParentName()));
        }
        visitClassifier(classDeclaration);
        return super.visit(classDeclaration);
    }

    @Override
    public Object visit(GlobalVariableListDeclaration globalVariableListDeclaration) {
        globalVariableListDeclaration.getScope().setParent(globalScope);
        return super.visit(globalVariableListDeclaration);
    }

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        variableDeclaration.setDataType(
                variableDeclaration.getTypeDeclaration()
                        .getDataType(globalScope));
        return null;
    }

    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        arrayTypeDeclaration.setBaseType(globalScope.resolveDataType(arrayTypeDeclaration.getTypeName()));
        return super.visit(arrayTypeDeclaration);
    }

    @Override
    public Object visit(Literal literal) {
        try {
            EnumerateType enumType = (EnumerateType) localScope.resolveDataType(literal.getDataTypeName());
            literal.setDataType(enumType);
        } catch (ClassCastException | DataTypeNotDefinedException e) {
        }
        return null;
    }

    @Override
    public Object visit(SymbolicReference ref) {
        String first = ref.getIdentifier();
        try {
            Any dataType = localScope.resolveDataType(first);
            EnumerateType et = (EnumerateType) dataType;
            String second = ((SymbolicReference) ref.getSub()).getIdentifier();
        } catch (ClassCastException | DataTypeNotDefinedException e) {

        }
        return null;
    }

    @Override
    public Object visit(InterfaceDeclaration interfaceDeclaration) {
        visitClassifier(interfaceDeclaration);
        return super.visit(interfaceDeclaration);
    }
}
