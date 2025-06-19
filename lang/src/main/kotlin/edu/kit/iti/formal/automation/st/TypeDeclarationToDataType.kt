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
package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.math.BigInteger

class TypeDeclarationToDataType(val scope: Scope) : AstVisitor<AnyDt?>() {
    override fun defaultVisit(obj: Any) = throw IllegalArgumentException("$obj is not handled")

    override fun visit(rtd: ReferenceTypeDeclaration) = ReferenceDt(rtd.refTo.accept(this)!!)

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) =
        EnumerateType(enumerationTypeDeclaration)

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): AnyDt {
        // val stringType = IECString
        // TODO
        return IECString.WSTRING
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): AnyDt {
        val rt = RecordType(structureTypeDeclaration.name)
        rt.fields += structureTypeDeclaration.fields
        return rt
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): AnyDt {
        val rt = RangeType()
        rt.name = subRangeTypeDeclaration.name
        rt.base = subRangeTypeDeclaration.baseType.obj as AnyInt
        if (subRangeTypeDeclaration.range != null) {
            rt.bottom = BigInteger.valueOf(subRangeTypeDeclaration.range?.startValue!!.toLong())
            rt.top = BigInteger.valueOf(subRangeTypeDeclaration.range?.stopValue!!.toLong())
        }
        return rt
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) = try {
        scope.resolveDataType(simpleTypeDeclaration.name)
    } catch (e: DataTypeNotDefinedException) {
        if (simpleTypeDeclaration.baseType.obj != null) {
            simpleTypeDeclaration.baseType.obj
        } else {
            if (simpleTypeDeclaration.baseType.identifier != null) {
                scope.resolveDataType(simpleTypeDeclaration.baseType.identifier!!)
            } else {
                null
            }
        }
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): AnyDt? {
        val atd = arrayTypeDeclaration.type.getDataType(scope)
        if (atd == null) return null
        val at = ArrayType(
            arrayTypeDeclaration.name,
            atd!!,
            arrayTypeDeclaration.ranges,
        )
        return at
    }
}