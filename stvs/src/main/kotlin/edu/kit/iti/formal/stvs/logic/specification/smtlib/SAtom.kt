package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory

/**
 * Represents an [SExpression] that is an atomic element.
 *
 * @author Carsten Csiky
 */
class SAtom : SExpression {
    private var string: String?

    /**
     * Creates an atomic expression from string.
     *
     * @param string string to represent
     */
    constructor(string: String?) {
        this.string = string
    }


    /**
     * Creates an atomic expression from S-Expression.
     *
     * @param s Expression
     */
    constructor(s: Sexp) {
        this.string = s.toString()
    }


    override val isAtom: Boolean
        get() = true

    override fun toSexpr(): Sexp? {
        return SexpFactory.newAtomicSexp(string)
    }

    override fun toString(): String {
        return "" + string + ""
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val atom = o as SAtom

        return if (string != null) string == atom.string else atom.string == null
    }


    override fun hashCode(): Int {
        return if (string != null) string.hashCode() else 0
    }

    override fun toText(): String? {
        return string
    }
}
