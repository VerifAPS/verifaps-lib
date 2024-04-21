package edu.kit.iti.formal.stvs.logic.io

/**
 * Indicates that an exception occurred during importing.
 *
 * @author Benjamin Alt
 */
class ImportException : Exception {

    /**
     * Create a new ImportException with a given error message.
     *
     * @param message The error message
     */
    constructor(message: String?) : super(message)

    /**
     * Create a new ImportException from a given Exception (e.g. an exception which was caught
     * during import).
     *
     * @param e The original exception
     */
    constructor(e: Exception?) : super(e)

    constructor(s: String?, e: Exception?) : super(s, e)
}
