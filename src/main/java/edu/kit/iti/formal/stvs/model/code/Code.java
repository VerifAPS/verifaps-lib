package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 09.01.17.
 */
public class Code {
    private List<Consumer<Code>> changeListeners;
    private List<Consumer<List<IOVariable>>> ioVariableListeners;
    private List<Consumer<ParsedCode>> parsedCodeListeners;
    private List<Consumer<List<SourcecodeToken>>> lexedCodeListeners;
    private ParsedCode parsedCode;
    private String filename;
    private String sourcecode;
    private List<SourcecodeToken> tokens;

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

    public void insertSourcecode(int position, String code) {

    }

    public List<SourcecodeToken> lexCode() {
        return null;
    }

    public void addSourcecodeListener(Consumer<String> listener) {

    }

    public void addIOVariablesListener(Consumer<List<IOVariable>> ioVariablesListener) {

    }

    public void addParsedCodeListener(Consumer<ParsedCode> parsedCodeListener) {

    }

    public void addLexedCodeListener(Consumer<List<SourcecodeToken>>){
        
    }


    public void setSourcecode(String sourcecode) {
        this.sourcecode = sourcecode;
    }
}
