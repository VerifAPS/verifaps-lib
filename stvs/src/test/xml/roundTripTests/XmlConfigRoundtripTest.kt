package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.config.GlobalConfig

import org.junit.Assert
import org.junit.jupiter.api.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.net.URISyntaxException

/**
 * Created by bal on 03.03.17.
 */
@RunWith(Parameterized::class)
class XmlConfigRoundtripTest(private val file: File) {
    @Test
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun configRoundtripTest() {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedConfig: GlobalConfig = ImporterFacade.importConfig(file)
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportConfig(importedConfig, ExporterFacade.ExportFormat.XML, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assert.assertEquals(
            TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter)
        )
    }

    companion object {
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<File?>? {
            return TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID)
        }
    }
}
