package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import de.tudresden.inf.lat.jsexp.SexpParserException

/**
 * Interface for al S-Expression compatible classes.
 *
 * @author Leon Kaucher
 */
interface SExpression {
    /**
     * Returns if instance is atomic.
     *
     * @return is atomic
     */
    val isAtom: Boolean

    /**
     * Convert to [Sexp].
     *
     * @return converted expression
     */
    fun toSexpr(): Sexp?

    /**
     * SExpression's textual representation.
     *
     * @return string containing the sexpression
     */
    fun toText(): String?

    companion object {
        /**
         * Creates an instance from a given string.
         *
         * @param string string to parse
         * @return instance which is represented by `string`
         */
        @JvmStatic
        fun fromText(string: String?): SExpression {
            try {
                val s = SexpFactory.parse(string)
                return fromSexp(s)
            } catch (exception: SexpParserException) {
                throw IllegalArgumentException(exception.message)
            }
        }


        /**
         * Creates an instance from a given [Sexp].
         *
         * @param s sexp that should be converted
         * @return instance which is represented by `s`
         */
        @JvmStatic
        fun fromSexp(s: Sexp): SExpression {
            return if (s.isAtomic) {
                SAtom(s)
            } else {
                SList(s)
            }
        }
    }
}
