package edu.kit.iti.formal.stvs.model.code;

import java.util.List;

/**
 * A {@code ParsedSyntaxErrorHandler} gets invoked by
 * {@link ParsedCode#parseCode(String, ParsedTokenHandler, ParsedSyntaxErrorHandler,
 * ParsedCodeHandler)} to notify about found syntaxErrors.
 */
@FunctionalInterface
public interface ParsedSyntaxErrorHandler {
  /**
   * This method must handle errors found while parsing.
   *
   * @param syntaxErrors A list of found syntax errors.
   */
  void accept(List<SyntaxError> syntaxErrors);
}
