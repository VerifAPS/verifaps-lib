package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.IoVariable
import java.util.*
import java.util.regex.Pattern

/**
 * Runtime-representation for variables in [Expression]s.
 * At this point it is not known whether this is a reference to a [FreeVariable] or an
 * [IoVariable]; it is simply the String name of either of those.
 *
 * @author Philipp
 */
class VariableExpr : Expression {
    val variableName: String?
    private val index: Optional<Int>

    /**
     * Constructs a new VariableExpr with a backwards reference.
     *
     * @param varName the name as a reference to a variable
     * @param index the index of the backwards-reference (for expressions like <tt>A[-1]</tt> for
     * example)
     */
    constructor(varName: String?, index: Int) {
        this.variableName = varName
        this.index = Optional.of(index)
    }

    /**
     * Constructs a new VariableExpr without a backwards reference.
     *
     * @param name the name as a reference to a variable.
     */
    constructor(name: String?) {
        this.variableName = name
        this.index = Optional.empty()
    }

    override fun <R> takeVisitor(visitor: ExpressionVisitor<R>): R? {
        return visitor.visitVariable(this)
    }

    fun getIndex(): Optional<Int>? {
        return index
    }

    fun equals(expr: VariableExpr): Boolean {
        return variableName == expr.variableName
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val that = o as VariableExpr

        if (if (variableName != null) variableName != that.variableName else that.variableName != null) {
            return false
        }
        return if (getIndex() != null) getIndex() == that.getIndex() else that.getIndex() == null
    }

    override fun hashCode(): Int {
        var result = if (variableName != null) variableName.hashCode() else 0
        result = 31 * result + (if (getIndex() != null) getIndex().hashCode() else 0)
        return result
    }

    override fun toString(): String {
        val indexStr = index.map { i: Int -> "[$i]" }.orElse("")
        return "VariableExpr(" + variableName + indexStr + ")"
    }

    companion object {
        @JvmField
        val IDENTIFIER_PATTERN: Pattern = Pattern.compile("[a-zA-Z_][\$a-zA-Z0-9_]*")
    }
}
