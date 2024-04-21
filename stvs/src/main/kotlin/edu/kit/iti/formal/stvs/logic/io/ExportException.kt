package edu.kit.iti.formal.stvs.logic.io

/**
 * Indicates that an error occurred during exporting.
 *
 * @author Benjamin Alt
 */
class ExportException : Exception {

    /**
     * Create a new ExportException with a given error message.
     * @param message The error message
     */
    constructor(message: String?) : super(message, null)

    /**
     * Create a new ExportException from an exception (e.g. an exception that was thrown and caught
     * during export).
     * @param exception The original exception
     */
    constructor(exception: Exception?) : super(exception)
}
