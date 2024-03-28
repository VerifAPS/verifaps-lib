package edu.kit.iti.formal.stvs.model.verification

import java.io.*
import java.nio.charset.StandardCharsets
import java.util.*

/**
 * Errors related to the verification process.
 *
 * @author Benjamin Alt
 */
class VerificationError : VerificationResult {
    private val reason: Reason
    override var logFile: File? = null

    /**
     * Construct a new VerificationError for a specific reason.
     *
     * @param reason The reason for the VerificationError
     */
    constructor(reason: Reason) {
        this.reason = reason
        this.logFile = null
    }

    /**
     * Construct a new VerificationError for a specific reason with a given log file.
     *
     * @param reason The reason for the VerificationError
     * @param logFile The log file
     */
    constructor(reason: Reason, logFile: File?) : this(reason) {
        this.logFile = logFile
    }

    /**
     * Construct a new VerificationError from an Exception (which was thrown while launching/managing
     * the verification. These will typically not come from the verification engine itself).
     *
     * @param ex The exception to construct a VerificationError from
     */
    constructor(ex: Exception) {
        this.reason = Reason.EXCEPTION
        try {
            val logFile = File.createTempFile("verification-exception", "")
            val writer = PrintWriter(
                OutputStreamWriter(FileOutputStream(logFile), StandardCharsets.UTF_8), true
            )
            ex.printStackTrace(writer)
        } catch (exception: IOException) {
            // Do nothing if writing the exception to the log throws an exception
            logFile = null
        }
        errorMessages[Reason.EXCEPTION] = ex.message
    }

    /**
     * Construct a new VerificationError from an Exception with a given log file.
     *
     * @param ex The exception to construct a VerificationError from
     * @param logFile The log file
     */
    constructor(ex: Exception, logFile: File?) {
        this.reason = Reason.EXCEPTION
        this.logFile = logFile
        errorMessages[Reason.EXCEPTION] =
            ex.message
    }

    val message: String?
        /**
         * Get an error message describing the error.
         *
         * @return An error message describing the error
         */
        get() = errorMessages[reason]

    override fun accept(visitor: VerificationResultVisitor) {
        visitor.visitVerificationError(this)
    }

    /**
     * Reasons why a [VerificationError] may occur.
     */
    enum class Reason {
        VERIFICATION_LAUNCH_ERROR, NUXMV_NOT_FOUND, PROCESS_ABORTED, TIMEOUT, ERROR, EXCEPTION, UNKNOWN
    }

    companion object {
        /* Error messages for the different error reasons */
        private val errorMessages: MutableMap<Reason, String?> = EnumMap(Reason::class.java)

        init {
            errorMessages[Reason.VERIFICATION_LAUNCH_ERROR] =
                ("The verification could not be launched. "
                        + "Check the verification engine command in the preferences dialog (Edit -> Preferences)")
            errorMessages[Reason.NUXMV_NOT_FOUND] =
                ("The nuXmv executable could not be found. "
                        + "Check the path to the nuXmv executable in the preferences dialog (Edit -> Preferences)")
            errorMessages[Reason.PROCESS_ABORTED] = "The verification process has been aborted."
            errorMessages[Reason.TIMEOUT] = "The verification timed out."
            errorMessages[Reason.ERROR] = "An error occurred during verification."
            errorMessages[Reason.UNKNOWN] = "An unknown error occurred during verification."
        }
    }
}
