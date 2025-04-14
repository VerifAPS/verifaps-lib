package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.IOException
import java.io.InputStream
import java.net.URISyntaxException
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlSessionImporterMalformedXmlTest {
    /**
     * Test whether importing malformed XML throws ImportExceptions.
     */
    @ParameterizedTest//(expected = ImportException::class)
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun sessionImporterMalformedXmlTest(name: String, file: InputStream) {
        assertFailsWith<ImportException> { ImporterFacade.importSession(file, GlobalConfig(), History()) }
    }

    companion object {
        @JvmStatic
        @Throws(URISyntaxException::class)
        fun testFiles() =
            (1..5).map { i ->
                Arguments.of(
                    "session_invalid_xml_$i.xml",
                    XmlConstraintSpecImporter::class.java.getResourceAsStream("session_invalid_xml_$i.xml")
                )
            }
    }
}
