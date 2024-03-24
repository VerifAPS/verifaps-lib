package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.logic.io.ImportException
import java.io.*

/**
 * An Interface for all classes concerned with importing model objects from some import format.
 * @param <T> "<u>T</u>o": Generic type parameter for the target type.
 * @author Benjamin Alt
</T> */
interface Importer<T> {
    /**
     * Must implement logic to implement `source`.
     *
     * @param source stream from which the data to import should be read
     * @return the imported object
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    fun doImport(source: InputStream?): T
}
