package edu.kit.iti.formal.stvs.model.code;

/**
 * A {@code ParsedCodeHandler} gets invoked after code parsing was successfully completed by.
 * {@link ParsedCode#parseCode(String, ParsedTokenHandler,
 * ParsedSyntaxErrorHandler, ParsedCodeHandler)}
 */
@FunctionalInterface
public interface ParsedCodeHandler {
  /**
   * This method must be implemented to handle the parsed code.
   *
   * @param code the parsed code
   */
  void accept(ParsedCode code);
}
