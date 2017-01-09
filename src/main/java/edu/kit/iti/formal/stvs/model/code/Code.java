package edu.kit.iti.formal.stvs.model.code;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 09.01.17.
 */
public class Code {
    private List<Consumer<Code>> changeListeners;
    private List<Consumer<List<IOVariable>>> ioVariableListeners;
    private List<Consumer<ParsedCode>> parsedCodeListeners;
    private ParsedCode parsedCode;
    private String filename;
    private String sourcecode;

    /**
     * creates a Dummy-Codefile
     */
    public Code(){

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

    public void insertSourcecode(int position, String code) {

    }

    public List<SourcecodeToken> lexCode() {
        return null;
    }

    public void addChangeListener(Consumer<Code> listener) {

    }

    public void addIOVariablesListener(Consumer<List<IOVariable>> ioVariablesListener) {

    }

    public void addParsedCodeListener(Consumer<ParsedCode> parsedCodeListener) {

    }
}
