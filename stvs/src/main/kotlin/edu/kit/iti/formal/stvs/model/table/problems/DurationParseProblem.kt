/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration

/**
 * The model for a [ParseException] in duration cells. (Generated when a duration cell
 * expression is <tt>[1,</tt> or <tt>[a,b]</tt>, etc.)
 */
data class DurationParseProblem
/**
 * Constructor for a Parse Problem for a given [ParseException].
 * Creates a better GUI message from the given exception.
 * @param exception the exception that occurred when parsing the duration cell
 * @param row the row of the duration cell that produced the given exception
 */
    (
    val exception: ParseException,
    override val row: Int
) : DurationProblem {
    override val errorMessage: String = createErrorMessage(exception)

    override val location = Selection("duration", row)

    companion object {
        /**
         * Tries to parse a duration into it's formal model [LowerBoundedInterval].
         * If that fails, it throws a [DurationParseProblem]
         * @param row the row of the duration to be parsed
         * @param duration the duration cell to be parsed
         * @return the formal model of a duration cell, if successfully parsed
         * @throws DurationParseProblem the parse problem if the duration could not be parsed
         */
        @Throws(SpecProblemException::class)
        fun tryParseDuration(row: Int, duration: ConstraintDuration): LowerBoundedInterval {
            try {
                return IntervalParser.parse(duration.asString ?: "")
            } catch (parseException: ParseException) {
                throw DurationParseProblem(parseException, row).asException()
            } catch (exception: IllegalStateException) {
                val parseException = ParseException(0, 0, exception.message!!)
                throw DurationParseProblem(parseException, row).asException()
            }
        }

        private fun createErrorMessage(exception: ParseException): String = exception.message ?: ""
    }
}