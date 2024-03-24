package edu.kit.iti.formal.stvs.model.expressions.parser

/**
 * A runtime exception which indicates the presence of unsupported exceptions in a cell
 * expression (see [UnsupportedExpressionException]). This is necessary because ANTLR-based
 * visitors cannot throw checked exceptions - runtime exceptions are unchecked, so this exception
 * should be used in classes derived from ANTLR-generated visitors.
 *
 * @author Philipp
 */
internal class UnsupportedExpressionRuntimeException(msg: String) : RuntimeException() {
    val exception: UnsupportedExpressionException = UnsupportedExpressionException(msg)
}
