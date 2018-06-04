package edu.kit.iti.formal.automation.analysis

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import lombok.RequiredArgsConstructor

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (25.06.17)
 */
@RequiredArgsConstructor
class FindDataTypes : AstVisitor<*> {
    private val globalScope: Scope? = null

    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        setParentScope(programDeclaration)
        globalScope!!.registerProgram(programDeclaration)
        programDeclaration.actions.forEach { n, a -> programDeclaration.scope.registerAction(a) }
        return null
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        setParentScope(functionBlockDeclaration)
        globalScope!!.registerFunctionBlock(functionBlockDeclaration)
        functionBlockDeclaration.actions.forEach(Consumer<ActionDeclaration> { functionBlockDeclaration.scope.registerAction(it) })
        return null
    }

    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        setParentScope(functionDeclaration)
        globalScope!!.registerFunction(functionDeclaration)
        return null
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): Any? {
        globalScope!!.registerType(subRangeTypeDeclaration)
        return null
    }

    override fun visit(variableDeclaration: VariableDeclaration<Initialization>): Any? {
        //weigl: do not register anonymous datatype, or references to data types.
        /*
        if (variableDeclaration.getTypeDeclaration() instanceof ArrayTypeDeclaration)
            variableDeclaration.getTypeDeclaration().accept(this);
        return super.visit(variableDeclaration);
        */
        return null
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration<*>): Any? {
        globalScope!!.registerType(simpleTypeDeclaration)
        return super.visit(simpleTypeDeclaration)
    }

    override fun visit(ptd: PointerTypeDeclaration): Any? {
        globalScope!!.registerType(ptd)
        return super.visit(ptd)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        setParentScope(clazz)
        globalScope!!.registerClass(clazz)
        return super.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
        setParentScope(interfaceDeclaration)
        globalScope!!.registerInterface(interfaceDeclaration)
        return super.visit(interfaceDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        globalScope!!.registerType(arrayTypeDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Any? {
        globalScope!!.registerType(enumerationTypeDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration): Any? {
        globalScope!!.registerType(stringTypeDeclaration)
        return null
    }

    override fun visit(typeDeclarations: TypeDeclarations): Any? {
        for (td in typeDeclarations)
            td.accept(this)
        return null
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): Any? {
        globalScope!!.registerType(structureTypeDeclaration)
        return null
    }

    override fun visit(gvl: GlobalVariableListDeclaration): Any? {
        globalScope!!.addVariables(gvl.scope)
        return super.visit(gvl)
    }

    private fun setParentScope(tle: HasScope<*>) {
        tle.scope.parent = globalScope
    }
}
