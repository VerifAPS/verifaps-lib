package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.*

import org.junit.jupiter.api.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.net.URISyntaxException

/**
 * @author Benjamin Alt
 */
@RunWith(Parameterized::class)
class XmlConstraintSpecImporterInvalidTest(private val file: File) {
    /**
     * Test whether ConstraintSpecifications with invalid data can be imported without throwing
     * exceptions. This must be possible since the user should not be prevented from importing and
     * ConstraintSpecifications containing syntax errors and other invalid data.
     * The conformance of the result of the import with the expected result is assured in other
     * unit tests (see [XmlConstraintSpecImporterTest],
     * [edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests.XmlConstraintSpecRoundtripTest]).
     */
    @Test
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecImporterInvalidTest() {
        ImporterFacade.importConstraintSpec(file, ImporterFacade.ImportFormat.XML)
    }

    companion object {
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<File> {
            val testFiles: MutableList<File> = ArrayList()
            for (i in 1..4) {
                testFiles.add(
                    File(
                        XmlConstraintSpecImporter::class.java.getResource(
                            "spec_constraint_invalid_data_$i.xml"
                        ).toURI().getPath()
                    )
                )
            }
            return testFiles
        }
    }
}
