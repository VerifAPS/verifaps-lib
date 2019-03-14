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

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) = EnumerateType(enumerationTypeDeclaration)

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): AnyDt {
        //val stringType = IECString
        //TODO
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

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) =
            try {
                scope.resolveDataType(simpleTypeDeclaration.name)
            } catch (e: DataTypeNotDefinedException) {
                if (simpleTypeDeclaration.baseType.obj != null)
                    simpleTypeDeclaration.baseType.obj
                else
                    if (simpleTypeDeclaration.baseType.identifier != null)
                        scope.resolveDataType(simpleTypeDeclaration.baseType.identifier!!)
                    else null
            }


    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): AnyDt? {
        val atd = arrayTypeDeclaration.type.getDataType(scope)
        if (atd == null) return null
        val at = ArrayType(arrayTypeDeclaration.name,
                atd!!,
                arrayTypeDeclaration.ranges)
        return at
    }


}

