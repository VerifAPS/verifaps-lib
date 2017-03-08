package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * Indicates that expressions which are not allowed in cell expressions (such as function
 * expressions) are encountered inside cell expressions. Generally thrown on all expressions that
 * the grammar supports, but our program does not (yet).
 *
 * @author Philipp
 */
public class UnsupportedExpressionException extends Exception {

  private final String unsupportedExpressionDescription;

  /**
   * Create a new UnsupportedExpressionException with a given description.
   * @param unsupportedExpressionDescription The description of the problematic grammar feature
   */
  public UnsupportedExpressionException(String unsupportedExpressionDescription) {
    super("Unsupported Grammar feature: " + unsupportedExpressionDescription);
    this.unsupportedExpressionDescription = unsupportedExpressionDescription;
  }

  public String getUnsupportedExpressionDescription() {
    return unsupportedExpressionDescription;
  }
}
