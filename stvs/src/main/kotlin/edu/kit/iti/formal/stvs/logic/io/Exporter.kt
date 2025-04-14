package edu.kit.iti.formal.stvs.logic.io

import java.io.ByteArrayOutputStream
import java.io.OutputStream

/**
 * Interface for all classes concerned with exporting model objects to some output format.
 * @param <F> "<u>F</u>rom": Generic type parameter for the source type.
 * @author Benjamin Alt
</F> */
interface Exporter<F> {
    /**
     * Implementations of this method must encode the `source` object. The format for encoding
     * is specified in the implementing classes or their subclasses. The encoded object is then
     * written to the returned [ByteArrayOutputStream].
     *
     * @param source Object that should be exported
     * @return The encoded object is written to this stream.
     * @throws ExportException Exception while exporting
     */
    @Throws(ExportException::class)
    fun export(source: F, target: OutputStream)
}
