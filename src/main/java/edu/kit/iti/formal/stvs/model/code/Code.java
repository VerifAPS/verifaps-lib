package edu.kit.iti.formal.stvs.model.code;

import java.util.List;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import javafx.beans.binding.Binding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;


/**
 * Created by csicar on 09.01.17.
 */
public class Code {

  /**
   * last valid parsed Code
   */
  private StringProperty filename;
  private List<RecognitionException> syntaxErrors;
  private StringProperty sourceCodeProperty;
  private NullableProperty<ParsedCode> parsedCode;
  private List<? extends Token> tokens;

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
        parsedCode -> this.parsedCode.set(parsedCode));
  }

  public void updateSourcecode(String sourcecode) {
    sourceCodeProperty.setValue(sourcecode);
    invalidate();
  }

  public String getSourcecode() {
    return sourceCodeProperty.get();
  }

  public List<RecognitionException> getSyntaxErrors() {
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
}
