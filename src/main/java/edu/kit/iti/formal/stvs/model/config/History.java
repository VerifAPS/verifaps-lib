package edu.kit.iti.formal.stvs.model.config;

import org.apache.commons.collections4.queue.CircularFifoQueue;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

/**
 * Contains information about recently opened code and spec files
 */
public class History {
  private CircularFifoQueue<String> codeFiles;
  private CircularFifoQueue<String> specFiles;

  public static final int HISTORY_DEPTH = 10;

  public History() {
    codeFiles = new CircularFifoQueue<String>(HISTORY_DEPTH);
    specFiles = new CircularFifoQueue<String>(HISTORY_DEPTH);
  }

  public History(Collection<String> codeFiles, Collection<String> specFiles) {
    if (codeFiles.size() > HISTORY_DEPTH || specFiles.size() > HISTORY_DEPTH) {
      // Don't silently cut off the part of the input collection that doesn't fit
      throw new IllegalArgumentException("List of filenames exceeds history size");
    }
    this.codeFiles = new CircularFifoQueue<String>(HISTORY_DEPTH);
    this.specFiles = new CircularFifoQueue<String>(HISTORY_DEPTH);

    for (String codeFilePath : codeFiles) {
      this.codeFiles.add(codeFilePath);
    }
    for (String specFilePath : specFiles) {
      this.specFiles.add(specFilePath);
    }
  }

  /**
   * Get the code file history
   *
   * @return A collection of filepaths of code files
   */
  public List<String> getCodeFiles() {
    return Arrays.asList(codeFiles.toArray(new String[0]));
  }

  /**
   * Get the spec file history
   *
   * @return A collection of filepaths of spec files
   */
  public List<String> getSpecFiles() {
    return Arrays.asList(specFiles.toArray(new String[0]));
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
