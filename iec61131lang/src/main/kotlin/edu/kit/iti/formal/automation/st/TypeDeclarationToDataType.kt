package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.math.BigInteger

class TypeDeclarationToDataType(val scope: Scope) : AstVisitor<AnyDt?>() {
    override fun defaultVisit(obj: Any) = throw IllegalArgumentException("$obj is not a type declaration")

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): AnyDt {
        //val stringType = IECString
        return stringTypeDeclaration.baseType.obj!!
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): AnyDt {
        val rt = RecordType()
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

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): AnyDt? {
        return scope.resolveDataType(simpleTypeDeclaration.name)
    }


    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): AnyDt {
        val at = ArrayType(arrayTypeDeclaration.name, arrayTypeDeclaration.baseType.obj!!, arrayTypeDeclaration.ranges)
        return at
    }
}

