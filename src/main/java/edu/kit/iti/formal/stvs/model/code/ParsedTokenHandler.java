package edu.kit.iti.formal.stvs.model.code;

import java.util.List;

import org.antlr.v4.runtime.Token;

/**
 * A {@code ParsedTokenHandler} gets invoked by
 * {@link ParsedCode#parseCode(String, ParsedTokenHandler,
 * ParsedSyntaxErrorHandler, ParsedCodeHandler)}.
 * to notify about lexed tokens Invariant: All tokens concatinized (re)produce the source code.
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
