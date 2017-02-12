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

  public void updateSourcecodeAsync(String sourcecode, Consumer<List<SyntaxError>> onSyntaxErrors) {
    sourceCodeProperty.set(sourcecode);
    ParsedCode.parseCode(sourceCodeProperty.get(),
        tokens -> this.tokens = tokens,
        syntaxErrors -> this.syntaxErrors = syntaxErrors,
        parsedCode -> this.parsedCode.set(parsedCode));
    onSyntaxErrors.accept(syntaxErrors);
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
