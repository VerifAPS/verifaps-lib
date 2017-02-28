package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import java.util.List;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import org.antlr.v4.runtime.Token;




/**
 * Created by csicar on 09.01.17.
 * @author Lukas
 * @author Philipp
 *        Represents the effective model of sourcecode.
 *        Extracts the formal model ({@link ParsedCode}).
 */
public class Code {

  private final StringProperty filename;
  private final StringProperty sourceCodeProperty;

  /**
   * last valid parsed Code.
   */
  private final NullableProperty<ParsedCode> parsedCode;
  private final ObservableList<Token> tokens;
  private final ObservableList<SyntaxError> syntaxErrors;


  /**
   * creates a default codefile.
   */
  public Code() {
    this("", "");
  }

  /**
   * creates a codefile which is invalidated.
   * @param filename name of the codefile
   * @param sourcecode content of the codefile
   */
  public Code(String filename, String sourcecode) {
    this.filename = new SimpleStringProperty(filename);
    this.sourceCodeProperty = new SimpleStringProperty(sourcecode);
    this.parsedCode = new NullableProperty<>();
    this.tokens = FXCollections.observableArrayList();
    this.syntaxErrors = FXCollections.observableArrayList();
    invalidate();
  }

  private void invalidate() {
    ParsedCode.parseCode(sourceCodeProperty.get(),
        this.tokens::setAll,
        this.syntaxErrors::setAll,
        this.parsedCode::set);
  }

  public void updateSourcecode(String sourcecode) {
    sourceCodeProperty.set(sourcecode);
    invalidate();
  }

  public String getSourcecode() {
    return sourceCodeProperty.get();
  }

  public StringProperty sourcecodeProperty() {
    return sourceCodeProperty;
  }

  public ObservableList<SyntaxError> syntaxErrorsProperty() {
    return syntaxErrors;
  }

  public ParsedCode getParsedCode() {
    return parsedCode.get();
  }

  public NullableProperty<ParsedCode> parsedCodeProperty() {
    return parsedCode;
  }

  public List<Token> getTokens() {
    return tokens;
  }

  public ObservableList<Token> tokensProperty() {
    return tokens;
  }

  public String getFilename() {
    return filename.get();
  }

  public void setFilename(String filename) {
    this.filename.set(filename);
  }

  public List<SyntaxError> getSyntaxErrors() {
    return syntaxErrors;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    Code code = (Code) obj;
    if (getFilename() != null ? !getFilename()
        .equals(code.getFilename()) : code.getFilename() != null) {
      return false;
    }
    if (getSourcecode() != null ? !getSourcecode().equals(code.getSourcecode()) : code
        .sourceCodeProperty != null) {
      return false;
    }
    if (getParsedCode() != null ? !getParsedCode().equals(code
        .getParsedCode()) : code.getParsedCode() != null) {
      return false;
    }
    if (getTokens() != null ? !getTokens().equals(code.getTokens()) : code.getTokens() != null) {
      return false;
    }
    /* ANTLR SyntaxError does not implement equals() properly
    return getSyntaxErrors() != null ? getSyntaxErrors().equals(code.getSyntaxErrors()) : code
    .getSyntaxErrors() == null; */
    if (getSyntaxErrors().size() != code.getSyntaxErrors().size()) {
      return false;
    }
    for (int i = 0; i < getSyntaxErrors().size(); i++) {
      if (!getSyntaxErrors().get(i).getMessage().equals(code.getSyntaxErrors().get(i)
          .getMessage())) {
        return false;
      }
    }
    return true;
  }
}
