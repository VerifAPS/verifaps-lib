package edu.kit.iti.formal.stvs.logic.io;

import java.io.InputStream;

/**
 * An Interface for all Importer-Classes.
 * @author Benjamin Alt
 */
public interface Importer<T> {
  /**
   * Must implement logic to implement {@code source}.
   *
   * @param source stream from which the data to import should be read
   * @return the imported object
   * @throws ImportException Exception while importing
   */
  public T doImport(InputStream source) throws ImportException;
}
