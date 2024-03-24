package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.parser.ExpressionParser
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException
import edu.kit.iti.formal.stvs.model.table.ConstraintCell

/**
 *
 *
 * A problem that is generated when a ConstraintCell inside a Constraint/HybridSpecification cannot
 * be parsed correctly (i.e. according to the antlr grammar file in <tt>src/main/antlr</tt>).
 *
 *
 * @author Benjamin Alt
 */
class CellParseProblem(exception: ParseException, column: String?, row: Int) :
    CellProblem(createErrorMessage(exception), column, row) {
    val parseException: ParseException = exception

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

        val that = obj as CellParseProblem

        return if (parseException != null) parseException == that.parseException else that.parseException == null
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (parseException != null) parseException.hashCode() else 0)
        return result
    }

    companion object {
        /**
         *
         *
         * Tries to create an [Expression] from the given string and context information.
         *
         *
         * @param typeContext the type context needed for parsing enums
         * @param columnId the column of the cell to check
         * @param row the row of the cell to check
         * @param cell the cell to parse
         * @return an [Expression]-AST (that might still be ill-typed)
         * @throws CellParseProblem if the expression could not be parsed
         * @throws CellUnsupportedExpressionProblem if the expression contains unsupported grammar
         * features (for example function calls)
         */
        @Throws(CellParseProblem::class, CellUnsupportedExpressionProblem::class)
        fun tryParseCellExpression(
            typeContext: List<Type>, columnId: String?, row: Int,
            cell: ConstraintCell?
        ): Expression {
            val parser = ExpressionParser(columnId, typeContext)
            try {
                return parser.parseExpression(cell?.asString)
            } catch (parseException: ParseException) {
                throw CellParseProblem(parseException, columnId, row)
            } catch (unsupportedException: UnsupportedExpressionException) {
                throw CellUnsupportedExpressionProblem(unsupportedException, columnId, row)
            }
        }

        private fun createErrorMessage(exception: ParseException): String? {
            return exception.message
        }
    }
}
