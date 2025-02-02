package edu.kit.iti.formal.stvs.model.code

/**
 * A `ParsedSyntaxErrorHandler` gets invoked by
 * [ParsedCode.parseCode] to notify about found syntaxErrors.
 */
fun interface ParsedSyntaxErrorHandler {
    /**
     * This method must handle errors found while parsing.
     *
     * @param syntaxErrors A list of found syntax errors.
     */
    fun accept(syntaxErrors: List<SyntaxError>)
}
