package edu.kit.iti.formal.stvs.logic.specification

/**
 * Exception that gets thrown if concretization fails in general.
 */
class ConcretizationException : Exception {
    override var message: String
        private set
    var originalException: Exception?
        private set

    constructor(message: String) {
        this.message = message
        originalException = null
    }

    /**
     * Creates an instance by wrapping an existent exception.
     *
     * @param e Exception that causes this exception
     */
    constructor(e: Exception) : super(e) {
        originalException = e
        message = e.message!!
    }
}
