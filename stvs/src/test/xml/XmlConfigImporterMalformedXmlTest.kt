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
class XmlConfigImporterMalformedXmlTest(private val file: File) {
    /**
     * Test whether importing malformed XML throws ImportExceptions.
     */
    @Test(expected = ImportException::class)
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun configImporterInvalidTest() {
        ImporterFacade.importConfig(file, ImporterFacade.ImportFormat.XML)
    }

    companion object {
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<File> {
            val testFiles: MutableList<File> = ArrayList()
            for (i in 1..5) {
                testFiles.add(
                    File(
                        XmlConstraintSpecImporter::class.java.getResource(
                            "config_invalid_xml_$i.xml"
                        ).toURI().getPath()
                    )
                )
            }
            return testFiles
        }
    }
}
