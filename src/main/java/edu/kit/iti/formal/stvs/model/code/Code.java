package edu.kit.iti.formal.stvs.model.code;

import java.util.List;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import javafx.application.Platform;
import javafx.beans.binding.Binding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;


/**
 * Created by csicar on 09.01.17.
 * @author  Philipp
 */
public class Code {

  private final StringProperty filename;
  private final StringProperty sourceCodeProperty;
  /**
   * last valid parsed Code
   */
  private final NullableProperty<ParsedCode> parsedCode;
  private final ObservableList<Token> tokens;
  private final ObservableList<SyntaxError> syntaxErrors;


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
}
