package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import javafx.beans.binding.Binding;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 09.01.17.
 */
public class Code {
  private List<Consumer<List<CodeIoVariable>>> ioVariableListeners;
  private List<Consumer<ParsedCode>> parsedCodeListeners;
  private List<Consumer<List<RecognitionException>>> syntaxErrorsListeners;
  private List<Consumer<List<Token>>> lexedCodeListeners;

  /**
   * last valid parsed Code
   */
  private ParsedCode parsedCode;
  private StringProperty  filename;
  private List<RecognitionException> syntaxErrors;
  private StringProperty sourceCodeProperty;
  private Binding<List<? extends Token>> tokensBinding;

  /**
   * creates a Dummy-Codefile
   */
  public Code() {
    this.filename.set("New Code");
    this.sourceCodeProperty = new SimpleStringProperty("");
    this.tokensBinding = createTokensBinding();
  }

  public Code(String filename, String sourcecode) {
    this.filename.set(filename);
    this.sourceCodeProperty = new SimpleStringProperty(sourcecode);
  }

  private Binding<List<? extends Token>> createTokensBinding() {
    return new ObjectBinding<List<? extends Token>>() {
      {
        bind(sourceCodeProperty);
      }

      @Override
      protected List<? extends Token> computeValue() {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(sourceCodeProperty.get()));
        return lexer.getAllTokens();
      }
    };
  }

  public StringProperty sourcecodeProperty() {
    return this.sourceCodeProperty;
  }

  public Binding<List<? extends Token>> tokensBinding() {
    return tokensBinding;
  }
}
