package edu.kit.iti.formal.stvs.model.table

/**
 * A concrete duration. A ConcreteDuration is localized in time, i.e. it is aware of the cycle in
 * which it begins.
 *
 * @author Benjamin Alt
 */
class ConcreteDuration(beginCycle: Int, duration: Int) {
    @JvmField
    val duration: Int

    @JvmField
    val beginCycle: Int

    /**
     * Construct a new concrete duration.
     *
     * @param beginCycle The cycle in which this duration begins
     * @param duration The duration
     */
    init {
        require(beginCycle >= 0) { "BeginCycle must be nonnegative" }
        require(duration >= 0) { "Duration must me nonnegative" }
        this.beginCycle = beginCycle
        this.duration = duration
    }

    val endCycle: Int
        get() = beginCycle + duration

    override fun toString(): String {
        return duration.toString()
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val duration1 = o as ConcreteDuration

        if (duration != duration1.duration) {
            return false
        }
        return beginCycle == duration1.beginCycle
    }

    override fun hashCode(): Int {
        var result = duration
        result = 31 * result + beginCycle
        return result
    }
}
