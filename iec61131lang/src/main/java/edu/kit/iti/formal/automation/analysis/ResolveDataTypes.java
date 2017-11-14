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
 * ResolveDataTypes searches and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl
 * @version 1
 * @since 25.11.16
 */
public class ResolveDataTypes extends AstVisitor<Object> {
    private final GlobalScope scope;
    private LocalScope local;

    public ResolveDataTypes() {
        this(GlobalScope.defaultScope());
    }

    public ResolveDataTypes(GlobalScope scope) {
        this.scope = scope;
    }

    private Any resolve(String name) {
        return scope.resolveDataType(name);
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setGlobalScope(scope);
        return super.visit(programDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setGlobalScope(scope);
        functionDeclaration.setReturnType(
                resolve(functionDeclaration.getReturnTypeName()));
        return super.visit(functionDeclaration);
    }

    @Override
    public Object visit(MethodDeclaration methodDeclaration) {
        methodDeclaration.setGlobalScope(scope);
        methodDeclaration.setReturnType(resolve(methodDeclaration.getReturnTypeName()));
        return super.visit(methodDeclaration);
    }

    @Override
    public Object visit(LocalScope localScope) {
        local = localScope;
        localScope.getLocalVariables().values()
                .forEach(vd -> vd.setDataType(resolve(vd.getDataTypeName())));
        return null;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setGlobalScope(scope);
        return super.visit(functionBlockDeclaration);
    }

    @Override
    public Object visit(ClassDeclaration classDeclaration) {
        classDeclaration.setGlobalScope(scope);
        return super.visit(classDeclaration);
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
                        .getDataType(scope));
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
            EnumerateType enumType = (EnumerateType)local.getGlobalScope().
                    resolveDataType(literal.getDataTypeName());
            literal.setDataType(enumType);
        } catch(ClassCastException | DataTypeNotDefinedException e) {}
        return null;
    }

    @Override
    public Object visit(SymbolicReference ref) {
        String first = ref.getIdentifier();
        try {
            Any dataType = local.getGlobalScope().resolveDataType(first);
            EnumerateType et = (EnumerateType) dataType;
            String second = ((SymbolicReference) ref.getSub()).getIdentifier();
        } catch (ClassCastException | DataTypeNotDefinedException e) {

        }
        return null;
    }
}
