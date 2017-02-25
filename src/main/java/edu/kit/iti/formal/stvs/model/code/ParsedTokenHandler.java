package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.Token;

import java.util.List;

/**
 * A {@code ParsedTokenHandler} gets invoked by
 * {@link ParsedCode#parseCode(String, ParsedTokenHandler, ParsedSyntaxErrorHandler, ParsedCodeHandler)}
 * to notify about lexed tokens
 */
@FunctionalInterface
public interface ParsedTokenHandler {
  /**
   * This method must handle the list of tokens generated while parsing code.
   *
   * @param tokenList List of lexed tokens
   */
  void accept(List<? extends Token> tokenList);
}
