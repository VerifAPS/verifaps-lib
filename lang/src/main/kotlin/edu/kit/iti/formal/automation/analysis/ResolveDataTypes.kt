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

import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.VOID
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * Search and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 25.11.16
 */
class ResolveDataTypes(val globalScope: Scope) : AstVisitorWithScope<Unit>() {
    init {
        scope = globalScope
    }

    override fun defaultVisit(obj: Any) {
        when (obj) {
            is TypeDeclaration -> obj.initialization?.accept(this)
        }
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        super.visit(functionDeclaration)
        functionDeclaration.returnType.resolve(scope::resolveDataType)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        if (functionBlockDeclaration.parent.identifier != null) {
            functionBlockDeclaration.parent.resolve(scope::resolveFunctionBlock)
        }
        return super.visit(functionBlockDeclaration)
    }

    override fun visit(localScope: Scope) {
        scope = localScope
        scope.variables.forEach { vd ->
            vd.accept(this)
        }
    }

    override fun visit(clazz: ClassDeclaration) {
        if (clazz.parent.identifier != null) {
            clazz.parent.resolve(scope::resolveClass)
            // assert(classDeclaration.parentClass != null)
        }
        val seq = clazz.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }
        return super.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        val seq = interfaceDeclaration.interfaces
        seq.forEach { it.resolve(scope::resolveInterface) }

        for (method in interfaceDeclaration.methods) {
            method.isAbstract = true
        }
        return super.visit(interfaceDeclaration)
    }

    override fun visit(method: MethodDeclaration) {
        super.visit(method)
        method.returnType.resolve(scope::resolveDataType)
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) = super.visit(gvlDecl)

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) = super.visit(arrayTypeDeclaration)

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        ignoreDataTypeNotDefined {
            simpleTypeDeclaration.baseType.resolve(scope::resolveDataType)
        }
        super.visit(simpleTypeDeclaration)
    }

    override fun visit(ref: SymbolicReference) {
        val first = ref.identifier
        try {
            // val dataType = scope.resolveDataType(first)
            // val et = dataType as EnumerateType?
            // ref.dataType = et
            /*if (ref.sub != null) {
                val second = (ref.sub as SymbolicReference).identifier
            }*/
        } catch (e: ClassCastException) {
        } catch (e: DataTypeNotDefinedException) {
        }
    }

    override fun visit(literal: Literal) {
        try {
            when (literal) {
                is IntegerLit -> {
                    literal.dataType.resolve(scope::resolveDataType0)
                    if (!literal.dataType.isIdentified) {
                        literal.dataType.obj = INT
                    }
                }
                is RealLit -> literal.dataType.resolve(scope::resolveDataType0)
                is EnumLit -> {
                    literal.dataType.resolve(scope::resolveDataType0)
                    if (!literal.dataType.isIdentified) {
                        literal.dataType.obj = scope.resolveEnumByValue(literal.value)
                    }
                }
                is StringLit -> literal.dataType.resolve(scope::resolveDataType0)
                is BitLit -> literal.dataType.resolve(scope::resolveDataType0)
                is UnindentifiedLit -> TODO()
                else -> {} // noting to-do, e.g., boolean literals, null literal
            }
        } catch (_: ClassCastException) {
        }
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        structureTypeDeclaration.fields.forEach { it.accept(this) }
    }

    override fun visit(it: VariableDeclaration) {
        it.typeDeclaration?.accept(this)
        ignoreDataTypeNotDefined { it.dataType = it.typeDeclaration?.getDataType(scope) }
    }

    override fun visit(invocation: InvocationStatement) {
        invocation.invoked = scope.resolveInvocation(invocation.callee)
        super.visit(invocation)
    }

    override fun visit(invocation: Invocation) {
        invocation.invoked = scope.resolveInvocation(invocation.callee)
        super.visit(invocation)
    }

    private fun ignoreDataTypeNotDefined(func: () -> Unit) {
        try {
            func()
        } catch (e: DataTypeNotDefinedException) {
        }
    }
}

class MaintainInitialValues : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}
    override fun visit(vd: VariableDeclaration) {
        if (vd.initValue != null) return
        vd.initValue = vd.init?.getValue()
        if (vd.initValue == null && vd.dataType != null && vd.dataType != VOID) {
            vd.initValue = DefaultInitValue.getInit(vd.dataType!!)
        }
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        super.visit(structureTypeDeclaration)
    }
}
