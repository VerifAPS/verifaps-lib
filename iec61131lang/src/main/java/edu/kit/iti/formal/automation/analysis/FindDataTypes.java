package edu.kit.iti.formal.automation.analysis;

/*-
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

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import lombok.RequiredArgsConstructor;

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
@RequiredArgsConstructor
public class FindDataTypes extends DefaultVisitor<Object> {
    private final GlobalScope globalScope;

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        globalScope.registerProgram(programDeclaration);
        return null;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        globalScope.registerFunctionBlock(functionBlockDeclaration);
        return null;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        globalScope.registerFunction(functionDeclaration);
        return null;
    }

    @Override
    public Object visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        globalScope.registerType(subRangeTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        globalScope.registerType(simpleTypeDeclaration);
        return super.visit(simpleTypeDeclaration);
    }

    @Override
    public Object visit(PointerTypeDeclaration ptd) {
        globalScope.registerType(ptd);
        return super.visit(ptd);
    }

    @Override
    public Object visit(ClassDeclaration clazz) {
        globalScope.registerClass(clazz);
        return super.visit(clazz);
    }

    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        globalScope.registerType(arrayTypeDeclaration);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        globalScope.registerType(enumerationTypeDeclaration);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StringTypeDeclaration stringTypeDeclaration) {
        globalScope.registerType(stringTypeDeclaration);
        return null;
    }

    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.accept(this);
        return null;
    }

    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        globalScope.registerType(structureTypeDeclaration);
        return null;
    }

}
