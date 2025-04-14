package edu.kit.iti.formal.stvs.model.expressions.parser

/**
 * An Exception for parsing errors.
 *
 * @author Philipp
 */
data class ParseException
/**
 * Any kind of parsing exception for human-readable files.
 *
 * @param line the first line the error occured
 * @param characterInLine the first character of the character in the line.
 * @param parseErrorMessage an error message to provide further information to the user.
 */
    (val line: Int, val characterInLine: Int, val parseErrorMessage: String) :
    Exception("(line $line character $characterInLine): $parseErrorMessage")
