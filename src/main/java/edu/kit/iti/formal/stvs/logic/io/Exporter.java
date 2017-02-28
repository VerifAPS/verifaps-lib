package edu.kit.iti.formal.stvs.logic.io;

import java.io.ByteArrayOutputStream;

/**
 * An Interface for all Exporter-Classes.
 *
 * @author Benjamin Alt
 */
public interface Exporter<F> {
  /**
   * Implementations of this method must encode the {@code source} object.
   * The format for encoding is specified in the implementing classes or their subclasses.
   * The encoded object is then written to the returned {@link ByteArrayOutputStream}.
   *
   * @param source Object that should be exported
   * @return The encoded object is written to this stream.
   * @throws ExportException Exception while exporting
   */
  public ByteArrayOutputStream export(F source) throws ExportException;
}
