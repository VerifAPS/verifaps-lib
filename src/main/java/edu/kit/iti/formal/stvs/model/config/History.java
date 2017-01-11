package edu.kit.iti.formal.stvs.model.config;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Contains information about recently opened code and spec files
 */
public class History {
    private ArrayList<String> codeFiles;
    private ArrayList<String> specFiles;

    /**
     * Get the code file history
     *
     * @return A list of filepaths of code files
     */
    public Collection<String> getCodeFiles() {
        return codeFiles;
    }

    /**
     * Get the spec file history
     *
     * @return A list of filepaths of spec files
     */
    public Collection<String> getSpecFiles() {
        return specFiles;
    }

    /**
     * Add the path to an opened code file to the history
     *
     * @param filename The path to the opened code file
     */
    public void addCodeFile(String filename) {

    }

    /**
     * Add the path to an opened spec file to the history
     *
     * @param filename The path to the opened spec file
     */
    public void addSpecFile(String filename) {

    }
}
