package edu.kit.iti.formal.stvs.model.code;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 09.01.17.
 */
public class Code {
    private List<Consumer<Code>> changeListeners;
    private List<Consumer<List<IOVariable>>> ioVariableListeners;
    private String filename;

    /**
     * creates a Dummy-Codefile
     */
    public Code(){

    }

    public Code(String filename, String sourceCode) {

    }

    public String getFilename() {
        return null
    }

    public void setFilename() {

    }

    public String getSourcecode() {
        return null;
    }

    public AST parseCode() {
        return null;
    }

    public List<IOVariable> extractVariables() {
        return null;
    }

    public List<Token> lexCode() {
        return null;
    }

    public void addChangeListener(Consumer<Code> listener) {

    }

    public void addIOVariablesListener(Consumer<List<IOVariable>>) {

    }
}
