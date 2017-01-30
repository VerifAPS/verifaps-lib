package edu.kit.iti.formal.stvs.logic.io;

import java.io.InputStream;

/**
 * @author Benjamin Alt
 */
public interface Importer<T> {
  public T doImport(InputStream source) throws ImportException;
}
