package edu.kit.iti.formal.stvs.model.common

/**
 * A problem concerning [FreeVariable]s.
 *
 * @author Philipp
 */
abstract class FreeVariableProblem
/**
 * Construct a new FreeVariableProblem with a given error message.
 * @param errorMessage The error message
 */ protected constructor(
    /**
     * Get the error message of this FreeVariableProblem.
     * @return The error message
     */
    @JvmField val errorMessage: String?
) : Exception() {
    val guiMessage: String
        /**
         *
         * This method can be used for showing text in the gui.
         *
         * @return a message suited for a dialog in the view
         */
        get() = problemName + ": " + errorMessage

    abstract val problemName: String
}
