/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (25.06.17)
 */
@Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
class RegisterDataTypes(val globalScope: Scope) : AstVisitorWithScope<Unit>() {
    init {
        scope = globalScope
    }

    override fun defaultVisit(obj: Any) {}

    override fun visit(elements: PouElements) {
        super.visit(elements)
    }

    override fun visit(pd: ProgramDeclaration) {
        scope.registerProgram(pd)
        goIntoScope(pd)
        pd.actions.forEach { a -> pd.scope.registerAction(a) }
        goOutoScope()
    }

    override fun visit(fbd: FunctionBlockDeclaration) {
        scope.registerFunctionBlock(fbd)
        goIntoScope(fbd)
        fbd.actions.forEach { scope.registerAction(it) }
        fbd.methods.forEach {
            scope.registerMethod(it)
            it.scope.parent = scope
        }
        goOutoScope()
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        scope.registerFunction(functionDeclaration)
        goIntoScope(functionDeclaration)
        goOutoScope()
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
        scope.registerType(subRangeTypeDeclaration)
    }

    override fun visit(variableDeclaration: VariableDeclaration) {
        // weigl: do not register anonymous datatype, or references to data types.
        /*
        if (variableDeclaration.getTypeDeclaration() instanceof ArrayTypeDeclaration)
            variableDeclaration.getTypeDeclaration().accept(this);
        return super.visit(variableDeclaration);
         */
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        scope.registerType(simpleTypeDeclaration)
        // super.visit(simpleTypeDeclaration)
    }

    override fun visit(ptd: PointerTypeDeclaration) {
        scope.registerType(ptd)
        return super.visit(ptd)
    }

    override fun visit(clazz: ClassDeclaration) {
        scope.registerClass(clazz)
        goIntoScope(clazz)
        clazz.methods.forEach {
            scope.registerMethod(it)
            it.scope.parent = scope
        }
        goOutoScope()
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        // goIntoScope(interfaceDeclaration)
        scope.registerInterface(interfaceDeclaration)
        // super.visit(interfaceDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        scope.registerType(arrayTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        scope.registerType(enumerationTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        scope.registerType(stringTypeDeclaration)
    }

    override fun visit(typeDeclarations: TypeDeclarations) {
        for (td in typeDeclarations) {
            td.accept(this)
        }
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        scope.registerType(structureTypeDeclaration)
    }

    override fun visit(gvl: GlobalVariableListDeclaration) {
        scope.addVariables(gvl.scope)
        gvl.scope = scope // global variables does not open an own scope.
        // return super.visit(gvl)
    }

    private fun goIntoScope(hasScope: HasScope) {
        if (scope != null) {
            hasScope.scope.parent = scope
        }
        scope = hasScope.scope
    }

    private fun goOutoScope() {
        scope = if (scope.parent != null) scope.parent!! else globalScope
    }
}