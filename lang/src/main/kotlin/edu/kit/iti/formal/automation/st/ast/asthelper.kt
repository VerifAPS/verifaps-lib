package edu.kit.iti.formal.automation.st.ast

import edu.kit.iti.formal.automation.datatypes.INT

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.06.19)
 */

/**
 * Creates an array access expression
 */
operator fun SymbolicReference.get(it: Iterable<Int>): SymbolicReference {
    val exprs = it.map { IntegerLit(INT, it.toBigInteger()) }
    return this.copy(subscripts = ExpressionList(exprs.toMutableList()))
}


operator fun SymbolicReference.get(fieldName: String): SymbolicReference = copy(sub = SymbolicReference(fieldName))


infix fun SymbolicReference.assignTo(init: Expression?) = AssignmentStatement(this, init!!)

infix fun String.assignTo(expr: Expression) = AssignmentStatement(SymbolicReference(this), expr)

infix fun String.assignTo(expr: String) =
        AssignmentStatement(SymbolicReference(this), SymbolicReference(expr))

