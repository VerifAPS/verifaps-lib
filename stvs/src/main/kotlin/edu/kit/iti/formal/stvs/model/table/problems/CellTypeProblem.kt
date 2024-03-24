package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintCell

/**
 * An instance is created when an [Expression] in a [ConstraintCell] is ill-typed.
 *
 * @author Benjamin Alt
 */
class CellTypeProblem(exception: TypeCheckException, column: String?, row: Int) :
    CellProblem(createErrorMessage(exception), column, row) {
    val typeCheckException: TypeCheckException? = exception

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }
        if (!super.equals(obj)) {
            return false
        }

        val that = obj as CellTypeProblem

        return if (typeCheckException != null) typeCheckException == that.typeCheckException else that.typeCheckException == null
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (typeCheckException != null) typeCheckException.hashCode() else 0)
        return result
    }

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
        @Throws(CellTypeProblem::class)
        fun tryTypeCheckCellExpression(
            typeChecker: TypeChecker, columnId: String?,
            row: Int, expr: Expression?
        ): Expression? {
            try {
                val type = typeChecker.typeCheck(expr)
                if (type!!.checksAgainst(TypeBool.Companion.BOOL)) {
                    return expr
                } else {
                    throw CellTypeProblem(
                        TypeCheckException(
                            expr, "The cell expression must evaluate to a boolean, "
                                    + "instead it evaluates to: " + type.typeName
                        ),
                        columnId, row
                    )
                }
            } catch (typeCheckException: TypeCheckException) {
                throw CellTypeProblem(typeCheckException, columnId, row)
            }
        }

        private fun createErrorMessage(exception: TypeCheckException): String? {
            return exception.message
        }
    }
}
