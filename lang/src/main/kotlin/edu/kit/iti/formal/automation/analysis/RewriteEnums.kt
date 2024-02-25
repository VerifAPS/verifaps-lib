package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.EnumLit
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import java.util.*

object RewriteEnums : AstMutableVisitor() {
    private var lastScope: Scope? = null

    override fun visit(localScope: Scope): Scope {
        lastScope = localScope
        return localScope
    }

    override fun visit(literal: Literal): Expression {
        when (literal) {
            is EnumLit -> literal.value = literal.value.uppercase(Locale.getDefault())
            else -> {}
        }
        return literal
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        val scope = lastScope
        if (scope != null) {
            val value = symbolicReference.identifier
            if (scope.resolveVariable(symbolicReference) == null) {
                val enum0 = scope.resolveEnumByValue(value)
                if (enum0 != null) return EnumLit(RefTo(enum0), value.uppercase(Locale.getDefault()))

                val enum1 = scope.resolveEnum(value)
                if (enum1 != null && symbolicReference.hasSub())
                    return EnumLit(RefTo(enum1), symbolicReference.sub!!.identifier.uppercase(Locale.getDefault()))
            }
        }
        return symbolicReference
    }
}
