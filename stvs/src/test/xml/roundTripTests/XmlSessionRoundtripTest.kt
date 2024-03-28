package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History

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
class XmlSessionRoundtripTest(private val file: File) {
    @Test
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun sessionRoundtripTest() {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSession: StvsRootModel = ImporterFacade.importSession(
            file,
            ImporterFacade.ImportFormat.XML, GlobalConfig(), History()
        )
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSession(importedSession, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assert.assertEquals(
            "ComparisonFailure at file: " + file.path, TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter)
        )
    }

    companion object {
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<File?>? {
            return TestUtils.getTestFiles(TestUtils.FileType.SESSION, TestUtils.Status.VALID)
        }
    }
}