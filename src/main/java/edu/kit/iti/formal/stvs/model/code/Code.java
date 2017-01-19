package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
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
  private String filename;
  private String sourcecode;
  private List<Token> tokens;
  private List<RecognitionException> syntaxErrors;
  private StringProperty sourceCodeProperty;

    /**
     * creates a Dummy-Codefile
     */
    public Code() {
        this.filename = "New Code";
        this.sourcecode = "";
        this.sourceCodeProperty = new SimpleStringProperty(this.sourcecode);
    }


    public Code(String filename, String sourcecode) {
        this.filename = filename;
        this.sourcecode = sourcecode;
        this.sourceCodeProperty = new SimpleStringProperty(this.sourcecode);
    }

  public String getFilename() {
    return filename;
  }

    public void setFilename(String newFilename) {
        this.filename = newFilename;
    }

  public String getSourcecode() {
    return sourcecode;
  }

  public void setSourcecode(String sourcecode) {
    this.sourcecode = sourcecode;
  }

  public void addSourcecodeListener(Consumer<String> listener) {

  }

  public void addLexedCodeListener(Consumer<List<Token>> lexed) {

  }

  public void addParsedCodeListener(Consumer<ParsedCode> parsedCodeListener) {

  }


  public List<RecognitionException> getSyntaxErrors() {
    return syntaxErrors;
  }

  public void setSyntaxErrors(List<RecognitionException> syntaxErrors) {
    this.syntaxErrors = syntaxErrors;
  }

  public void addSyntaxErrorsListener(Consumer<List<RecognitionException>> listener) {

  }

  public StringProperty sourcecodeProperty() {
    return this.sourceCodeProperty;
  }
}
