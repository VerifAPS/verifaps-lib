package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.IoVariable
import java.util.regex.Pattern

/**
 * Runtime-representation for variables in [Expression]s.
 * At this point it is not known whether this is a reference to a [FreeVariable] or an
 * [IoVariable]; it is simply the String name of either of those.
 *
 * @author Philipp
 */
data class VariableExpr(val variableName: String?, val index: Int? = null) : Expression() {
    override fun <R> accept(visitor: ExpressionVisitor<R>): R {
        return visitor.visitVariable(this)
    }

    fun equals(expr: VariableExpr): Boolean {
        return variableName == expr.variableName
    }


    override fun toString(): String {
        val indexStr = index?.let { "[$it]" } ?: ""
        return "VariableExpr($variableName$indexStr)"
    }

    companion object {
        @JvmField
        val IDENTIFIER_PATTERN: Pattern = Pattern.compile("[a-zA-Z_][\$a-zA-Z0-9_]*")
    }
}
