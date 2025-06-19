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
package edu.kit.iti.formal.automation.datatypes

import edu.kit.iti.formal.automation.analysis.Reporter
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration
import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration
import java.util.*
import java.util.concurrent.Callable

class DataTypeAssignability(val expected: AnyDt) : DataTypeVisitorNN<Boolean> {
    val reporter = Reporter()

    override fun defaultVisit(obj: Any): Boolean = false

    override fun visit(enumerateType: EnumerateType): Boolean {
        if (enumerateType.name == expected.name) {
            return true
        }
        return false
    }

    override fun visit(anyBit: AnyBit): Boolean = when (expected) {
        is AnyBit -> expected.bitLength >= AnyBit.BOOL.bitLength
        else -> false
    }

    override fun visit(dateAndTime: AnyDate.DATE_AND_TIME): Boolean = when (expected) {
        is AnyDate.DATE -> true
        is AnyDate.DATE_AND_TIME -> true
        else -> false
    }

    override fun visit(timeOfDay: AnyDate.TIME_OF_DAY): Boolean = expected == timeOfDay
    override fun visit(date: AnyDate.DATE): Boolean = expected == date

    override fun visit(arrayType: ArrayType): Boolean =
        TODO("not implemented") // To change body of created functions use File | Settings | File Templates.

    override fun visit(anyInt: AnyInt): Boolean = when (expected) {
        // TODO There should be a conformance check somewhere else!
        is AnyInt -> (anyInt.isSigned == expected.isSigned && anyInt.bitLength <= expected.bitLength) ||
            (anyInt.bitLength < expected.bitLength)
        // TODO automatic conversion for bits?
        else -> false
    }

    override fun visit(timeType: TimeType): Boolean = expected is TimeType

    override fun visit(reference: ReferenceDt): Boolean {
        TODO("not implemented") // To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(recordType: RecordType): Boolean {
        when (expected) {
            is RecordType -> {
                expected.fields.forEach { required ->
                    val f = recordType.fields.get(required.name) ?: return false
                    required.dataType?.let {
                        // TODO: recursion on this visitor
                        if (f.dataType?.isAssignableTo(it) == false) {
                            return false
                        }
                    }
                }
            }
            else -> {}
        }
        return false
    }

    override fun visit(classDataType: ClassDataType): Boolean = when (classDataType) {
        is ClassDataType.ClassDt -> {
            val types = classDataType.clazz.getAllSuperTypes()
            expected in types
        }
        is ClassDataType.InterfaceDt -> {
            val types = classDataType.clazz.getAllSuperTypes()
            expected in types
        }
        is ClassDataType.AnyClassDt -> {
            false
        }
    }

    override fun visit(functionBlockDataType: FunctionBlockDataType): Boolean = super.visit(functionBlockDataType)
}

class FindAllSuperTypes : Callable<List<ClassDataType>> {
    val clazzesToSearch = Stack<ClassDeclaration>()
    val interfazestoSearch = Stack<InterfaceDeclaration>()
    val found: MutableList<ClassDataType> = arrayListOf()

    override fun call(): List<ClassDataType> {
        searchClasses()
        searchInterfaces()
        return found
    }

    private fun searchClasses() {
        while (clazzesToSearch.isNotEmpty()) {
            val c = clazzesToSearch.pop()!!
            found.add(ClassDataType.ClassDt(c))
            addClass(c)
        }
    }

    fun addClass(c: ClassDeclaration) {
        c.parent.obj?.let { clazzesToSearch.add(it) }
        c.interfaces.forEach { it.obj?.let { addInterface(it) } }
    }

    fun addInterface(declaration: InterfaceDeclaration) {
        interfazestoSearch.add(declaration)
    }

    private fun searchInterfaces() {
        while (interfazestoSearch.isNotEmpty()) {
            val c = interfazestoSearch.pop()!!
            found.add(ClassDataType.InterfaceDt(c))
            c.interfaces.forEach { it.obj?.let { interfazestoSearch.add(it) } }
        }
    }
}

private fun ClassDeclaration.getAllSuperTypes(): List<ClassDataType> {
    val fast = FindAllSuperTypes()
    fast.addClass(this)
    return fast.call()
}

private fun InterfaceDeclaration.getAllSuperTypes(): List<ClassDataType> {
    val fast = FindAllSuperTypes()
    fast.addInterface(this)
    return fast.call()
}