package edu.kit.iti.formal.stvs.model.code

/**
 * A `ParsedCodeHandler` gets invoked after code parsing was successfully completed by.
 * [ParsedCode.parseCode]
 */
fun interface ParsedCodeHandler {
    /**
     * This method must be implemented to handle the parsed code.
     *
     * @param code the parsed code
     */
    fun accept(code: ParsedCode?)
}
