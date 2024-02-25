package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import java.io.*
import java.net.URL
import java.nio.file.Path
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (15.06.17)
 * @version 2 (22.07.18)
 */
object IECXMLFacade {
    fun extractPLCOpenXml(url: URL, sink: Writer) {
        PCLOpenXMLBuilder(url, CodeWriter(sink)).run()
        sink.flush()
    }

    fun extractPLCOpenXml(filename: String, sink: Writer) = extractPLCOpenXml(File(filename), sink)
    fun extractPLCOpenXml(filename: File, sink: Writer) = extractPLCOpenXml(filename.toURI().toURL(), sink)
    fun extractPLCOpenXml(filename: Path, sink: Writer) = extractPLCOpenXml(filename.toUri().toURL(), sink)

    fun extractPLCOpenXml(filename: URL): String {
        val writer = StringWriter()
        extractPLCOpenXml(filename, writer)
        return writer.toString()
    }

    fun extractPLCOpenXml(filename: String) = extractPLCOpenXml(File(filename))
    fun extractPLCOpenXml(filename: File) = extractPLCOpenXml(filename.toURI().toURL())
    fun extractPLCOpenXml(filename: Path) = extractPLCOpenXml(filename.toUri().toURL())


    val SFC_KEYWORDS = setOf("step", "end_step", "transition", "end_transition")
    fun quoteVariable(name: String): String =
        if (name.lowercase(Locale.getDefault()) in SFC_KEYWORDS) "`$name`" else name

    fun quoteStBody(body: String): String {
        return body.replace("\\b\\w+\\b".toRegex()) {
            quoteVariable(it.value)
        }
    }
}
