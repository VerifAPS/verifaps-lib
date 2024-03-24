package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval
import edu.kit.iti.formal.stvs.model.expressions.parser.*
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration

/**
 *
 *
 * The model for a [ParseException] in duration cells. (Generated when a duration cell
 * expression is <tt>[1,</tt> or <tt>[a,b]</tt>, etc.)
 *
 *
 * @author Benjamin Alt
 */
class DurationParseProblem
/**
 *
 *
 * Constructor for a Parse Problem for a given [ParseException].
 *
 *
 *
 *
 * Creates a better GUI message from the given exception.
 *
 *
 * @param exception the exception that occurred when parsing the duration cell
 * @param row the row of the duration cell that produced the given exception
 */
    (exception: ParseException, row: Int) : DurationProblem(createErrorMessage(exception), row) {
    companion object {
        /**
         *
         *
         * Tries to parse a duration into it's formal model [LowerBoundedInterval].
         *
         *
         *
         *
         * If that fails, it throws a [DurationParseProblem]
         *
         *
         * @param row the row of the duration to be parsed
         * @param duration the duration cell to be parsed
         * @return the formal model of a duration cell, if successfully parsed
         * @throws DurationParseProblem the parse problem if the duration could not be parsed
         */
        @Throws(DurationParseProblem::class)
        fun tryParseDuration(row: Int, duration: ConstraintDuration): LowerBoundedInterval {
            try {
                return IntervalParser.Companion.parse(duration.asString)
            } catch (parseException: ParseException) {
                throw DurationParseProblem(parseException, row)
            }
        }

        private fun createErrorMessage(exception: ParseException): String? {
            return exception.message
        }
    }
}
