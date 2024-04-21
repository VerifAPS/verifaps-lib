package edu.kit.iti.formal.stvs.model.expressions

/**
 * A visitor for [Expression]s.
 *
 * @param <R> the return type of this visit. It has to be defined at the class-level, because all
 * implemented methods must return the same type.
 * @author Philipp
</R> */
interface ExpressionVisitor<R> {
    fun visitBinaryFunction(binary: BinaryFunctionExpr): R

    fun visitUnaryFunction(unary: UnaryFunctionExpr): R

    fun visitLiteral(literal: LiteralExpr): R

    fun visitVariable(expr: VariableExpr): R

    fun visit(expr: GuardedExpression): R
}
