package edu.kit.iti.formal.stvs.logic.io.xml.verification

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.junit.Assert
import org.junit.jupiter.api.Test
import java.io.File
import java.io.IOException
import java.net.URISyntaxException
import java.nio.file.Paths

/**
 * @author Benjamin Alt
 */
class GeTeTaExporterTest {
    @Test
    @Throws(ImportException::class, IOException::class, ExportException::class, URISyntaxException::class)
    fun testExport() {
        val stream = loadFromTestSets("/valid_1/constraint_spec_valid_1.xml")
        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            stream, ImporterFacade.ImportFormat.XML
        )
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSpec(constraintSpec, ExporterFacade.ExportFormat.GETETA, tempFile)
        val expectedString = TestUtils.readFromFile(
            Paths.get(StvsApplication::class.java.getResource("testSets/valid_1/geteta_input_valid_1.xml").toURI())
                .toString()
        )
        val actualString = TestUtils.readFromFile(tempFile.absolutePath)
        Assert.assertEquals(
            TestUtils.removeWhitespace(expectedString),
            TestUtils.removeWhitespace(actualString)
        )
    }
}