package edu.kit.iti.formal.stvs.model.expressions

/**
 * The runtime representation for intervals that possibly have no upper bound, but have a guaranteed
 * lower bound.
 *
 * @author Benjamin Alt
 */
data class LowerBoundedInterval
/**
 * Creates an instance of an interval.
 *
 * @param lowerBound the lower bound for this interval
 * @param upperBound the optional upper bound for this interval
 */(val lowerBound: Int, val upperBound: Int? = null) {
    init {
        require(lowerBound >= 0)
        upperBound?.let {
            require(it >= 0)
            require(it >= lowerBound)
        }
    }
}
