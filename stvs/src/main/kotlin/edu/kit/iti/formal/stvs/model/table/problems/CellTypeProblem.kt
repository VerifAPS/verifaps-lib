package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeCheckException
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker
import edu.kit.iti.formal.stvs.model.table.ConstraintCell

/**
 * An instance is created when an [Expression] in a [ConstraintCell] is ill-typed.
 *
 * @author Benjamin Alt
 */
data class CellTypeProblem(val exception: TypeCheckException, override val column: String, override val row: Int) :
    CellProblem {

    override val errorMessage: String = createErrorMessage(exception)
    override val location: Selection = Selection(column, row)

    companion object {
        /**
         *
         *
         * Either the given expression is well-typed and evaluates to a boolean and is returned, or a
         * [CellTypeProblem] is thrown.
         *
         *
         * @param typeChecker type checker for checking the type of this cell
         * @param columnId the column of the expression to check
         * @param row the row of the expression to check
         * @param expr the expression to type-check for illness / not evaluating to boolean
         * @return an expression that **must** evaluate to true
         * @throws CellTypeProblem a problem if the expression does not evaluate to a boolean or is
         * ill-typed
         */
        @JvmStatic
        @Throws(SpecProblemException::class)
        fun tryTypeCheckCellExpression(
            typeChecker: TypeChecker,
            columnId: String,
            row: Int,
            expr: Expression
        ): Expression {
            try {
                val type = typeChecker.typeCheck(expr)
                if (type!!.checksAgainst(TypeBool)) {
                    return expr
                } else {
                    throw CellTypeProblem(
                        TypeCheckException(
                            expr, "The cell expression must evaluate to a boolean, "
                                    + "instead it evaluates to: " + type.typeName
                        ),
                        columnId, row
                    ).asException()
                }
            } catch (typeCheckException: TypeCheckException) {
                throw CellTypeProblem(typeCheckException, columnId, row).asException()
            }
        }

        private fun createErrorMessage(exception: TypeCheckException) = exception.message ?: ""
    }
}
