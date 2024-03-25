package edu.kit.iti.formal.stvs.model.expressions.parser

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.maximum
import edu.kit.iti.formal.automation.testtables.builder.minimum
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval
import org.antlr.v4.runtime.*
import java.util.*

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
            return LowerBoundedInterval(duration.minimum, Optional.ofNullable(duration.maximum))
        }
    }
}
