package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.Token;

/**
 * Represents a syntax error in code.
 *
 * @author Lukas Fritsch
 */
public class SyntaxError {
  private int line;
  private int charPos;
  private String message;

  /**
   *  creates a syntax error.
   * @param line the line of the token with the syntax error
   * @param charPos the char position of the token with the syntax error
   * @param message the error message
   */
  public SyntaxError(int line, int charPos, String message) {
    this.line = line;
    this.charPos = charPos;
    this.message = message;
  }


  public int getLine() {
    return line;
  }

  public int getCharPos() {
    return charPos;
  }

  public String getMessage() {
    return message;
  }

  public boolean isToken(Token token) {
    return (line == token.getLine()) && (charPos == token.getCharPositionInLine());
  }

  public String toString() {
    return "Error at (" + line + "," + charPos + "): " + message;
  }
}
