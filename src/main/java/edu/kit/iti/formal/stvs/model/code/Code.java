package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import javafx.beans.binding.Binding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ObservableValue;
import org.antlr.v4.runtime.ANTLRInputStream;
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
  private NullableProperty<ParsedCode> parsedCode;
  private StringProperty filename;
  private List<RecognitionException> syntaxErrors;
  private StringProperty sourceCodeProperty;
  private Binding<List<? extends Token>> tokensBinding;

  /**
   * creates a Dummy-Codefile
   */
  public Code() {
    this.filename = new SimpleStringProperty("New Code");
    this.sourceCodeProperty = new SimpleStringProperty("");
    this.tokensBinding = createTokensBinding();
    this.parsedCode = new NullableProperty<ParsedCode>(null);

    sourceCodeProperty.addListener(this::rebuildParsedCode);
  }

  public Code(String filename, String sourcecode) {
    this.filename = new SimpleStringProperty(filename);
    this.sourceCodeProperty = new SimpleStringProperty(sourcecode);
    this.tokensBinding = createTokensBinding();
    this.parsedCode = new NullableProperty<ParsedCode>(ParsedCode.parseCode(sourceCodeProperty.get()));

    sourceCodeProperty.addListener(this::rebuildParsedCode);
  }

  private void rebuildParsedCode(ObservableValue<? extends String> observableValue, String oldVal, String newVal) {
    parsedCode.set(ParsedCode.parseCode(newVal));
  }

  private Binding<List<? extends Token>> createTokensBinding() {
    return new ObjectBinding<List<? extends Token>>() {
      {
        bind(sourceCodeProperty);
      }

      @Override
      protected List<? extends Token> computeValue() {
        return Code.this.computeTokens(Code.this.sourcecodeProperty().get());
      }
    };
  }

  public void invalidate() {

  }

  public List<? extends Token> computeTokens(String sourcecode) {
    IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(sourcecode));
    return lexer.getAllTokens();
  }

  public StringProperty sourcecodeProperty() {
    return this.sourceCodeProperty;
  }

  public Binding<List<? extends Token>> tokensBinding() {
    return tokensBinding;
  }

  public NullableProperty<ParsedCode> parsedCodeProperty() {
    return parsedCode;
  }

  public Optional<ParsedCode> computeParsedCode(String sourcecode) {
    return null;
  }
}
