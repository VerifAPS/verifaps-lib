package edu.kit.iti.formal.stvs.logic.io;

import java.io.OutputStream;

/**
 * @author Benjamin Alt
 */
public interface Exporter<F> {
  public OutputStream export(F source) throws ExportException;
}
