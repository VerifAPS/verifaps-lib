package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import org.antlr.v4.runtime.Token;

import java.util.List;


/**
 * Created by csicar on 09.01.17.
 */
public class Code {

  /**
   * last valid parsed Code
   */
  private StringProperty filename;
  private StringProperty sourceCodeProperty;
  private NullableProperty<ParsedCode> parsedCode;
  private List<? extends Token> tokens;
  private List<SyntaxError> syntaxErrors;
  private ObservableList<SyntaxError> syntaxErrorObs;


  /**
   * creates a Dummy-Codefile
   */
  public Code() {
    this("", "");
  }

  public Code(String filename, String sourcecode) {
    this.filename = new SimpleStringProperty(filename);
    this.sourceCodeProperty = new SimpleStringProperty(sourcecode);
    this.parsedCode = new NullableProperty<>();
    syntaxErrorObs = FXCollections.observableArrayList();


    invalidate();
  }

  private void invalidate() {
    ParsedCode.parseCode(sourceCodeProperty.get(),
        tokens -> this.tokens = tokens,
        syntaxErrors -> this.syntaxErrors = syntaxErrors,
        parsedCode -> this.parsedCode.set(parsedCode));
    syntaxErrorObs.setAll(syntaxErrors);
  }

  public void updateSourcecode(String sourcecode) {
    sourceCodeProperty.setValue(sourcecode);
    invalidate();
  }

  public String getSourcecode() {
    return sourceCodeProperty.get();
  }

  public List<SyntaxError> getSyntaxErrors() {
    return syntaxErrors;
  }

  public ObservableList<SyntaxError> getSyntaxErrorObs() { return syntaxErrorObs;}

  public ParsedCode getParsedCode() {
    return parsedCode.get();
  }

  public NullableProperty<ParsedCode> parsedCodeProperty() {
    return parsedCode;
  }

  public List<? extends Token> getTokens() {
    return tokens;
  }

  public String getFilename() {
    return filename.get();
  }

  public void setFilename(String filename) {
    this.filename.set(filename);
  }
}
