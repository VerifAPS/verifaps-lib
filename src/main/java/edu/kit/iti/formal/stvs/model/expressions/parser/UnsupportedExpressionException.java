package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * An Exception invoked, when expressions like function expressions are
 * encountered inside cell-expressions. Generally thrown on all expressions
 * that the grammar supports, but our program does not yet.
 * @author Philipp
 */
public class UnsupportedExpressionException extends Exception {

  private final String unsupportedExpressionDescription;

  public UnsupportedExpressionException(String unsupportedExpressionDescription) {
    super("Unsupported Grammar feature: " + unsupportedExpressionDescription);
    this.unsupportedExpressionDescription = unsupportedExpressionDescription;
  }

  public String getUnsupportedExpressionDescription() {
    return unsupportedExpressionDescription;
  }
}
