package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.Token;

/**
 * Created by Lukas on 02.02.2017.
 *
 * @author Lukas Fritsch
 *         <p>
 *         Represents a syntax error in code
 */
public class SyntaxError {
  private int line;
  private int charPos;
  private String message;

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
