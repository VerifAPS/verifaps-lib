package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.junit.Assert
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
class XmlConstraintSpecRoundtripTest(private val file: File) {
    @Test
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecRoundtripTest() {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            file,
            ImporterFacade.ImportFormat.XML
        )
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assert.assertEquals(
            "ComparisonFailure at File:" + file.path, TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter)
        )
    }

    companion object {
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<File?>? {
            return TestUtils.getTestFiles(TestUtils.FileType.CONSTRAINT, TestUtils.Status.VALID)
        }
    }
}
