package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection

/*
* A problem concerning a specification table.
* @author Philipp
*/
abstract class SpecProblem
/**
 * Create a new SpecProblem with a given error message and for a given location.
 * @param errorMessage The error message
 * @param location The location of the problem
 */(@JvmField val errorMessage: String?, private val location: Selection) : Exception(
    errorMessage
) {
    fun getLocation(): Selection? {
        return location
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val that = o as SpecProblem

        if (if (errorMessage != null) errorMessage != that.errorMessage
            else that.errorMessage != null
        ) {
            return false
        }
        return if (getLocation() != null) getLocation() == that.getLocation() else that.getLocation() == null
    }

    override fun hashCode(): Int {
        var result = if (errorMessage != null) errorMessage.hashCode() else 0
        result = 31 * result + (if (getLocation() != null) getLocation().hashCode() else 0)
        return result
    }
}
