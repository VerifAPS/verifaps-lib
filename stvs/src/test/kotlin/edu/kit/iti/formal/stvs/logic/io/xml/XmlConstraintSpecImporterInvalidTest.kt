package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.IOException
import java.io.InputStream
import java.net.URISyntaxException

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporterInvalidTest {
    /**
     * Test whether ConstraintSpecifications with invalid data can be imported without throwing
     * exceptions. This must be possible since the user should not be prevented from importing and
     * ConstraintSpecifications containing syntax errors and other invalid data.
     * The conformance of the result of the import with the expected result is assured in other
     * unit tests (see [XmlConstraintSpecImporterTest],
     * [edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests.XmlConstraintSpecRoundtripTest]).
     */
    @ParameterizedTest
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecImporterInvalidTest(name: String, file: InputStream) {
        ImporterFacade.importConstraintSpec(file)
    }

    companion object {
        @JvmStatic
        @Throws(URISyntaxException::class)
        fun testFiles() =
            (1..4).map { i ->
                Arguments.of(
                    "spec_constraint_invalid_data_$i.xml",
                    XmlConstraintSpecImporter::class.java.getResourceAsStream("spec_constraint_invalid_data_$i.xml")
                )
            }
    }
}
