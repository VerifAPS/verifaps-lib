package edu.kit.iti.formal.stvs.model.expressions.parser

import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval
import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionParser.Fixed_intervalContext
import org.antlr.v4.runtime.*
import java.util.*

/**
 * A class for parsing fixed interval expressions like <tt>[1,-]</tt> or <tt>[1,5]</tt>, defined by
 * the ANTLR grammar in antlr/CellExpression.g4. This parser does not need any context information
 * and does not capture state and thus is a singleton.
 *
 * @author Philipp
 */
class IntervalParser : CellExpressionBaseVisitor<LowerBoundedInterval?>() {
    override fun visitFixed_interval(ctx: Fixed_intervalContext): LowerBoundedInterval {
        // If the Interval is a simple interval like [1,3] or [5,-]
        if (ctx.a != null && ctx.b != null) {
            val lowerBound = parsePositive(ctx.a)
            val upperBoundString = ctx.b.text

            if ("-" == upperBoundString) {
                return LowerBoundedInterval(lowerBound, Optional.empty())
            } else {
                val upperBoundInt = parsePositive(ctx.b)
                if (upperBoundInt < lowerBound) {
                    throw ParseRuntimeException(
                        ParseException(
                            ctx.b.line,
                            ctx.b.charPositionInLine, "Upper bound is lower than lower bound"
                        )
                    )
                }
                return LowerBoundedInterval(lowerBound, Optional.of(upperBoundInt))
            }
            // if the interval string is just a constant, like "6" -> [6,6]
        } else if (ctx.c != null) {
            val value = parsePositive(ctx.c)
            return LowerBoundedInterval(value, Optional.of(value))
        }
        // Only case left is the wildcard "-"
        return LowerBoundedInterval(0, Optional.empty())
    }

    private fun parsePositive(token: Token): Int {
        val number = token.text.toInt()
        if (number < 0) {
            throw ParseRuntimeException(
                ParseException(
                    token.line,
                    token.charPositionInLine, "Interval boundary must be positive."
                )
            )
        }
        return number
    }

    companion object {
        private val INSTANCE = IntervalParser()

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
        fun parse(intervalAsString: String?): LowerBoundedInterval {
            val charStream: CharStream = ANTLRInputStream(intervalAsString)
            val lexer = CellExpressionLexer(charStream)
            val tokens: TokenStream = CommonTokenStream(lexer)
            val parser = CellExpressionParser(tokens)
            parser.removeErrorListeners()
            parser.addErrorListener(ThrowingErrorListener())
            try {
                val ctx = parser.fixed_interval()
                    ?: throw ParseException(0, 0, "Expected fixed interval")
                return INSTANCE.visit(ctx)!!
            } catch (runtimeException: ParseRuntimeException) {
                throw runtimeException.parseException
            }
        }
    }
}
