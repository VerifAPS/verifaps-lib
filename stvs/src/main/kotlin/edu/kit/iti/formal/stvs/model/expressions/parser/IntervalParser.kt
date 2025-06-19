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
package edu.kit.iti.formal.stvs.model.expressions.parser

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.minimum
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval

/**
 * A class for parsing fixed interval expressions like <tt>[1,-]</tt> or <tt>[1,5]</tt>, defined by
 * the ANTLR grammar in antlr/CellExpression.g4. This parser does not need any context information
 * and does not capture state and thus is a singleton.
 *
 * @author Philipp
 */
class IntervalParser {
    companion object {
        /**
         * Parse an interval, for example <tt>[1,-]</tt> or <tt>-</tt> (a wildcard) or <tt>[1,4]</tt>.
         * Only fixed values are allowed, no variables.
         *
         * @param intervalAsString the string to be parsed.
         * @return a LowerBoundedInterval as the runtime representation of interval strings.
         * @throws ParseException in case the string doesn't fit the given fixed-interval grammar.
         */
        @JvmStatic
        @Throws(ParseException::class)
        fun parse(intervalAsString: String): LowerBoundedInterval {
            val duration = GetetaFacade.parseDuration(intervalAsString)
            return LowerBoundedInterval(duration.minimum, duration.upper)
        }
    }
}

private val Duration.upper: Int?
    get() = when (this) {
        is Duration.OpenInterval -> null
        is Duration.ClosedInterval -> upper
        is Duration.Omega -> null
    }