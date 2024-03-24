package edu.kit.iti.formal.stvs.model.verification

import java.io.File
import java.util.*

/**
 * A [VerificationResult] indicating a successful verification (i.e. the code verified
 * against the specification).
 * @author Benjamin Alt
 */
class VerificationSuccess(override val logFile: File) : VerificationResult {
    override fun accept(visitor: VerificationResultVisitor) {
        visitor.visitVerificationSuccess(this)
    }
}
