package edu.kit.iti.formal.automation;

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
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import jdk.nashorn.internal.objects.Global;

/**
 * <p>ResolveDataTypes class.</p>
 *
 * @author Alexander Weigl
 * @version 1 (25.11.16)
 */
public class ResolveDataTypes extends DefaultVisitor<Object> {
    private GlobalScope scope = new GlobalScope();

    private boolean registerPhase = true;

    /**
     * <p>Constructor for ResolveDataTypes.</p>
     */
    public ResolveDataTypes() {
    }

    /**
     * <p>Constructor for ResolveDataTypes.</p>
     *
     * @param scope a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public ResolveDataTypes(GlobalScope scope) {
        this.scope = scope;
    }


    /**
     * <p>resolve.</p>
     *
     * @param tle a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     * @return a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public static GlobalScope resolve(TopLevelElements tle) {
        GlobalScope globalScope = GlobalScope.defaultScope();
        ResolveDataTypes rdt = new ResolveDataTypes(globalScope);
        tle.visit(rdt);
        rdt.registerPhase = false;
        tle.visit(rdt);
        return globalScope;
    }

    private Any resolve(String name) {
        return scope.resolveDataType(name);
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerProgram(programDeclaration);
        else
            programDeclaration.getLocalScope().visit(this);
        return super.visit(programDeclaration);
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerFunction(functionDeclaration);
        else {
            functionDeclaration.setReturnType(
                    resolve(functionDeclaration.getReturnTypeName()));
            functionDeclaration.getLocalScope().visit(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(LocalScope localScope) {
        localScope.getLocalVariables().values().forEach(
                vd -> vd.setDataType(resolve(vd.getDataTypeName()))
        );
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setGlobalScope(scope);
        if (registerPhase)
            scope.registerFunctionBlock(functionBlockDeclaration);
        else
            functionBlockDeclaration.getLocalScope().visit(this);
        return super.visit(functionBlockDeclaration);
    }


    /** {@inheritDoc} */
    @Override
    public Object visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        if (registerPhase) scope.registerType(subRangeTypeDeclaration);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        if (registerPhase) scope.registerType(simpleTypeDeclaration);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        if (!registerPhase) { //every data type is registered
            variableDeclaration.setDataType(
                    variableDeclaration.getTypeDeclaration().getDataType(scope));
        }
        return null;
    }


    /** {@inheritDoc} */
    @Override
    public Object visit(PointerTypeDeclaration ptd) {
        if (registerPhase) scope.registerType(ptd);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        if (registerPhase) scope.registerType(arrayTypeDeclaration);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        if (registerPhase) scope.registerType(enumerationTypeDeclaration);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(StringTypeDeclaration stringTypeDeclaration) {
        if (registerPhase) scope.registerType(stringTypeDeclaration);

        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.visit(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        if (registerPhase) scope.registerType(structureTypeDeclaration);
        return null;
    }

}
