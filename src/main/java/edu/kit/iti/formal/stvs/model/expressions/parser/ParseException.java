package edu.kit.iti.formal.stvs.model.expressions.parser;

/**
 * An Exception for parsing errors.
 *
 * @author Philipp
 */
public class ParseException extends Exception {

  private final int line;
  private final int characterInLine;
  private final String parseErrorMessage;

  /**
   * Any kind of parsing exception for human-readable files.
   *
   * @param line              the first line the error occured
   * @param characterInLine   the first character of the character in the line.
   * @param parseErrorMessage an error message to provide further information to the user.
   */
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

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    ParseException that = (ParseException) o;

    if (getLine() != that.getLine()) {
      return false;
    }
    if (getCharacterInLine() != that.getCharacterInLine()) {
      return false;
    }
    return getParseErrorMessage() != null ? getParseErrorMessage().equals(that.getParseErrorMessage()) : that.getParseErrorMessage() == null;
  }

  @Override
  public int hashCode() {
    int result = getLine();
    result = 31 * result + getCharacterInLine();
    result = 31 * result + (getParseErrorMessage() != null ? getParseErrorMessage().hashCode() : 0);
    return result;
  }
}
