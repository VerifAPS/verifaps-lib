package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * Created by philipp on 18.01.17.
 */
public class ParseException extends Exception {

  private final int line;
  private final int characterInLine;
  private final String parseErrorMessage;

  public ParseException(int line, int characterInLine, String parseErrorMessage) {
    super("(line " + line + " character " + characterInLine + "): " + parseErrorMessage);
    this.line = line;
    this.characterInLine = characterInLine;
    this.parseErrorMessage = parseErrorMessage;
  }

  public int getLine() {
    return line;
  }

  public int getCharacterInLine() {
    return characterInLine;
  }

  public String getParseErrorMessage() {
    return parseErrorMessage;
  }
}
