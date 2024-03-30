package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.runners.Parameterized
import java.io.IOException
import java.io.InputStream
import java.net.URISyntaxException
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporterMalformedXmlTest {
    /**
     * Test whether importing malformed XML throws ImportExceptions.
     */
    @ParameterizedTest//(expected = ImportException::class)
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecImporterInvalidTest(name: String, file: InputStream) {
        assertFailsWith<ImportException> {
            ImporterFacade.importConstraintSpec(file)
        }
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles() = (1..6).map { i ->
            Arguments.of(
                "spec_constraint_invalid_xml_$i.xml",
                XmlConstraintSpecImporter::class.java.getResourceAsStream(
                    "spec_constraint_invalid_xml_$i.xml"
                )
            )
        }
    }
}
