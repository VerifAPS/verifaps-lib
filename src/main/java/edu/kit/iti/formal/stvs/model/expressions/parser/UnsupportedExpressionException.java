package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * Created by philipp on 18.01.17.
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
