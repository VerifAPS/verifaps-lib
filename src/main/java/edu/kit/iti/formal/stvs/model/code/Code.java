package edu.kit.iti.formal.stvs.model.code;

import java.util.List;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import javafx.beans.binding.Binding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.Optional;


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

  /**
   * creates a Dummy-Codefile
   */
  public Code() {
    this("New Code", "");
  }

  public Code(String filename, String sourcecode) {
    this.filename = new SimpleStringProperty(filename);
    this.sourceCodeProperty = new SimpleStringProperty(sourcecode);
    this.parsedCode = new NullableProperty<>();

    invalidate();
  }

  private void invalidate() {
    ParsedCode.parseCode(sourceCodeProperty.get(),
        tokens -> this.tokens = tokens,
        syntaxErrors -> this.syntaxErrors = syntaxErrors,
        parsedCode -> this.parsedCode.set(parsedCode));
  }

  public void updateSourcecode(String sourcecode) {
    sourceCodeProperty.setValue(sourcecode);
    invalidate();
  }

  public String getSourcecode() {
    return sourceCodeProperty.get();
  }

  public List<? extends SyntaxError> getSyntaxErrors() {
    return syntaxErrors;
  }

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
}
