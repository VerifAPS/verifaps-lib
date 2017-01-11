package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;

import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 09.01.17.
 */
public class Code {
    private List<Consumer<List<CodeIOVariable>>> ioVariableListeners;
    private List<Consumer<ParsedCode>> parsedCodeListeners;
    private List<Consumer<List<ANTLRSyntaxError>>> syntaxErrorsListeners;
    private List<Consumer<List<Token>>> lexedCodeListeners;

    /**
     * last valid parsed Code
     */
    private ParsedCode parsedCode;
    private String filename;
    private String sourcecode;
    private List<Token> tokens;
    private List<ANTLRSyntaxError> syntaxErrors;

    /**
     * creates a Dummy-Codefile
     */
    public Code() {

    }

    public Code(String filename, String sourceCode) {

    }

    public String getFilename() {
        return filename;
    }

    public void setFilename() {

    }

    public String getSourcecode() {
        return sourcecode;
    }

    public void setSourcecode(String sourcecode) {
        this.sourcecode = sourcecode;
    }

    public void addSourcecodeListener(Consumer<String> listener) {

    }

    public void addLexedCodeListener(Consumer<List<Token>> lexed){

    }

    public void addParsedCodeListener(Consumer<ParsedCode> parsedCodeListener) {

    }


    public List<ANTLRSyntaxError> getSyntaxErrors() {
        return syntaxErrors;
    }

    public void setSyntaxErrors(List<ANTLRSyntaxError> syntaxErrors) {
        this.syntaxErrors = syntaxErrors;
    }

    public void addSyntaxErrorsListener(Consumer<List<ANTLRSyntaxError>> listener) {

    }
}
