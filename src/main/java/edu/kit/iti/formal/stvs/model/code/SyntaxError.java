package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.Token;

/**
 * Created by Lukas on 02.02.2017.
 */
public class SyntaxError {
  private Token token;

  public SyntaxError(Token token) {
    this.token = token;
  }


  public Token getToken() {
    return token;
  }

  public String toString() {
    return "SyntaxError(" + token + ")";
  }

  public boolean isSameToken(Token token) {
    return token.getStartIndex() == this.token.getStartIndex() &&
        token.getText().equals(this.token.getText());
  }
}
