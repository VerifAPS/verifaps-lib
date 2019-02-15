package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import java.io.*
import java.net.URL
import java.nio.file.Path

/**
 * @author Alexander Weigl
 * @version 1 (15.06.17)
 * @version 2 (22.07.18)
 */
object IECXMLFacade {
    fun extractPLCOpenXml(stream: Reader, sink: Writer) {
        PCLOpenXMLBuilder(stream, CodeWriter(sink))
        sink.flush()
    }

    fun extractPLCOpenXml(stream: InputStream, sink: Writer) = extractPLCOpenXml(stream.reader(), sink)
    fun extractPLCOpenXml(filename: URL, sink: Writer) =
            filename.openStream().use {
                IECXMLFacade.extractPLCOpenXml(it, sink)
            }

    fun extractPLCOpenXml(filename: String, sink: Writer) = extractPLCOpenXml(File(filename), sink)
    fun extractPLCOpenXml(filename: File, sink: Writer) = extractPLCOpenXml(filename.toURI().toURL(), sink)
    fun extractPLCOpenXml(filename: Path, sink: Writer) = extractPLCOpenXml(filename.toUri().toURL(), sink)

    fun extractPLCOpenXml(filename: Reader): String {
        val writer = StringWriter()
        extractPLCOpenXml(filename, writer)
        return writer.toString()
    }

    fun extractPLCOpenXml(filename: InputStream): String = filename.reader().use { extractPLCOpenXml(it) }

    fun extractPLCOpenXml(filename: URL): String =
            filename.openStream().use { IECXMLFacade.extractPLCOpenXml(it) }

    fun extractPLCOpenXml(filename: String) = extractPLCOpenXml(File(filename))
    fun extractPLCOpenXml(filename: File) = extractPLCOpenXml(filename.toURI().toURL())
    fun extractPLCOpenXml(filename: Path) = extractPLCOpenXml(filename.toUri().toURL())
}
