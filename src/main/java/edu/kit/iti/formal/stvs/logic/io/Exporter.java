package edu.kit.iti.formal.stvs.logic.io;

import java.io.ByteArrayOutputStream;

/**
 * @author Benjamin Alt
 */
public interface Exporter<F> {
  public ByteArrayOutputStream export(F source) throws ExportException;
}
