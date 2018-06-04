package edu.kit.iti.formal.automation.analysis


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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import lombok.`val`

/**
 * Search and set the data type attributes based on the given global scope.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 25.11.16
 */
class ResolveDataTypes(private val globalScope: Scope) : AstVisitor<Any>() {

    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        super.visit(programDeclaration)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        super.visit(functionDeclaration)
        functionDeclaration.returnType = currentScope.resolveDataType(functionDeclaration.returnTypeName!!)
        return null
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): Any? {
        visit(functionBlockDeclaration)
        return super.visit(functionBlockDeclaration)
    }

    override fun visit(localScope: Scope): Any? {
        currentScope = localScope
        currentScope.parent = globalScope

        localScope.variables.values.forEach { vd ->
            vd.dataType = currentScope.resolveDataType(vd.dataTypeName!!)
            if (vd.init != null) {
                vd.init!!.accept<Any>(this)
            }
        }
        return null
    }

    override fun visit(variableDeclaration: VariableDeclaration<Initialization>): Any? {
        variableDeclaration.dataType = variableDeclaration.typeDeclaration!!
                .getDataType(globalScope)
        return null
    }

    override fun visit(classDeclaration: ClassDeclaration): Any? {
        if (classDeclaration.parent.identifier != null) {
            classDeclaration.parent.setIdentifiedObject(
                    classDeclaration.scope.resolveClass(classDeclaration.parent.identifier))
            assert(classDeclaration.parentClass != null)
        }
        val seq = classDeclaration.interfaces
        seq.forEach { face -> face.setIdentifiedObject(classDeclaration.scope.resolveInterface(face.identifier)) }
        return super.visit(classDeclaration)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
        val seq = interfaceDeclaration.interfaces
        seq.forEach { face -> face.setIdentifiedObject(interfaceDeclaration.scope.resolveInterface(face.identifier)) }
        return super.visit(interfaceDeclaration)
    }

    override fun visit(methodDeclaration: MethodDeclaration): Any? {
        super.visit(methodDeclaration)
        methodDeclaration.returnType = currentScope.resolveDataType(methodDeclaration.returnTypeName!!)
        return null
    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): Any? {
        globalVariableListDeclaration.scope.parent = globalScope
        return super.visit(globalVariableListDeclaration)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        arrayTypeDeclaration.baseType = globalScope.resolveDataType(arrayTypeDeclaration.typeName!!)
        return super.visit(arrayTypeDeclaration)
    }

    override fun visit(ref: SymbolicReference): Any? {
        val first = ref.identifier
        try {
            val dataType = currentScope.resolveDataType(first)
            val et = dataType as EnumerateType?
            ref.dataType = et
            if (ref.sub != null) {
                val second = (ref.sub as SymbolicReference).identifier
                // TODO...?
            }
        } catch (e: ClassCastException) {

        } catch (e: DataTypeNotDefinedException) {
        }

        return null
    }

    override fun visit(literal: Literal): Any? {
        try {
            literal.dataType = currentScope.resolveDataType(literal.dataTypeName!!)
        } catch (e: ClassCastException) {
        } catch (e: DataTypeNotDefinedException) {
        }

        return null
    }

}
