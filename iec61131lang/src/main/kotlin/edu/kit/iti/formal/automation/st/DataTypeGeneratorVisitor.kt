package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.ast.ArrayTypeDeclaration
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable

class DataTypeGeneratorVisitor() : DefaultVisitor<AnyDt>() {
    override fun defaultVisit(obj: Any?): AnyDt? {
        return super.defaultVisit(obj)
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): AnyDt? {
        return super.visit(arrayTypeDeclaration)
    }
}
