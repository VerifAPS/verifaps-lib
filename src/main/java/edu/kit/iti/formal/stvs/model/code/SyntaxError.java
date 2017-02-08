package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.Token;

/**
 * Created by Lukas on 02.02.2017.
 */
public class SyntaxError {
  private int line;
  private int charPos;

  public SyntaxError(int line, int charPos) {
    this.line = line;
    this.charPos = charPos;
  }


  public int getLine() {
    return line;
  }
  public int getCharPos() {return charPos;}

  public boolean isToken(Token token) {
    return (line == token.getLine()) && (charPos == token.getCharPositionInLine());
  }

  public String toString() {
    return "SyntaxError(" + line + "," + charPos+ ")";
  }
/*
  public boolean isSameToken(Token token) {
    return token.getStartIndex() == this.token.getStartIndex() &&
        token.getText().equals(this.token.getText());
  }
*/
}
