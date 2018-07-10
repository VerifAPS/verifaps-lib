package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.EnumLit
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor

object RewriteEnums : AstMutableVisitor() {
    private lateinit var lastScope: Scope

    override fun visit(localScope: Scope): Scope {
        lastScope = localScope
        return lastScope
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        if (lastScope.resolveVariable(symbolicReference) == null) {
            val enum0 = lastScope.resolveEnumByValue(symbolicReference.identifier)
            if (enum0 != null) return EnumLit(RefTo(enum0), symbolicReference.identifier)
            val enum1 = lastScope.resolveEnum(symbolicReference.identifier)
            if (enum1 != null && symbolicReference.hasSub())
                return EnumLit(RefTo(enum1), symbolicReference.sub!!.identifier)
        }
        return symbolicReference
    }
}
