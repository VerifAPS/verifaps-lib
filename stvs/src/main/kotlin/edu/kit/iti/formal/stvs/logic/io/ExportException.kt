package edu.kit.iti.formal.stvs.logic.io

/**
 * Indicates that an error occurred during exporting.
 *
 * @author Benjamin Alt
 */
class ExportException(message: String, originalException: Exception? = null) : Exception(message, originalException) {
}
