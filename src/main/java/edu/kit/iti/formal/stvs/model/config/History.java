package edu.kit.iti.formal.stvs.model.config;

import java.util.ArrayList;
import java.util.List;

/**
 * Contains information about recently opened code and spec files
 */
public class History {
  private List<String> codeFiles;
  private List<String> specFiles;

  public History() {
    codeFiles = new ArrayList<>();
    specFiles = new ArrayList<>();
  }

  /**
   * Get the code file history
   *
   * @return A list of filepaths of code files
   */
  public List<String> getCodeFiles() {
    return codeFiles;
  }

  /**
   * Get the spec file history
   *
   * @return A list of filepaths of spec files
   */
  public List<String> getSpecFiles() {
    return specFiles;
  }

  /**
   * Add the path to an opened code file to the history
   *
   * @param filename The path to the opened code file
   */
  public void addCodeFile(String filename) {
    codeFiles.add(filename);
  }

  /**
   * Add the path to an opened spec file to the history
   *
   * @param filename The path to the opened spec file
   */
  public void addSpecFile(String filename) {
    specFiles.add(filename);
  }
}
