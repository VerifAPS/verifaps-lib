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
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

/**
 * Searche and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 25.11.16
 */
public class ResolveDataTypes extends AstVisitor<Object> {
    private final GlobalScope globalScope;

    public ResolveDataTypes(GlobalScope globalScope) {
        this.globalScope = globalScope;
    }

    private Any resolve(String name) {
        return globalScope.resolveDataType(name);
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setGlobalScope(globalScope);
        return super.visit(programDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setGlobalScope(globalScope);
        functionDeclaration.setReturnType(
                resolve(functionDeclaration.getReturnTypeName()));
        return super.visit(functionDeclaration);
    }

    @Override
    public Object visit(MethodDeclaration methodDeclaration) {
        methodDeclaration.setGlobalScope(globalScope);
        methodDeclaration.setReturnType(resolve(methodDeclaration.getReturnTypeName()));
        return super.visit(methodDeclaration);
    }

    @Override
    public Object visit(LocalScope localScope) {
        localScope.getLocalVariables().values()
                .forEach(vd -> vd.setDataType(resolve(vd.getDataTypeName())));
        return super.visit(localScope);
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setGlobalScope(globalScope);
        return super.visit(functionBlockDeclaration);
    }

    @Override
    public Object visit(ClassDeclaration classDeclaration) {
        classDeclaration.setGlobalScope(globalScope);
        return super.visit(classDeclaration);
    }

    @Override
    public Object visit(InterfaceDeclaration interfaceDeclaration) {
        interfaceDeclaration.setGlobalScope(globalScope);
        return super.visit(interfaceDeclaration);
    }

    @Override
    public Object visit(GlobalVariableListDeclaration globalVariableListDeclaration) {
        globalVariableListDeclaration.setGlobalScope(globalScope);
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
            EnumerateType enumType = (EnumerateType) currentLocalScope.getGlobalScope().
                    resolveDataType(literal.getDataTypeName());
            literal.setDataType(enumType);
        } catch(ClassCastException | DataTypeNotDefinedException e) {}
        return null;
    }
}
