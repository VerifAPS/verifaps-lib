package edu.kit.iti.formal.stvs.model.expressions

import java.util.*

/**
 * The runtime representation for intervals that possibly have no upper bound, but have a guaranteed
 * lower bound.
 *
 * @author Benjamin Alt
 */
class LowerBoundedInterval
/**
 * Creates an instance of an interval.
 *
 * @param lowerBound the lower bound for this interval
 * @param upperBound the optional upper bound for this interval
 */(@JvmField val lowerBound: Int, @JvmField val upperBound: Optional<Int>) {
    override fun equals(other: Any?): Boolean {
        if (this === other) {
            return true
        }
        if (other !is LowerBoundedInterval) {
            return false
        }

        val that = other

        if (lowerBound != that.lowerBound) {
            return false
        }
        return upperBound == that.upperBound
    }

    override fun hashCode(): Int {
        var result = lowerBound
        result = 31 * result + upperBound.hashCode()
        return result
    }

    override fun toString(): String {
        return ("LowerBoundedInterval(" + lowerBound + ","
                + (if (upperBound.isPresent) upperBound.get() else "-") + ")")
    }
}
