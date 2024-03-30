package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File
import java.io.IOException
import java.net.URISyntaxException

/**
 * Created by bal on 03.03.17.
 */
class XmlConfigRoundtripTest {
    @ParameterizedTest
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun configRoundtripTest(file:File) {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedConfig: GlobalConfig = ImporterFacade.importConfig(file)
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportConfig(importedConfig, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assertions.assertEquals(
            TestUtils.removeWhitespace(fileContentsAfter),
            TestUtils.removeWhitespace(fileContentsBefore)
        )
    }

    companion object {
        @JvmStatic
        @Throws(URISyntaxException::class)
        fun testFiles(): Collection<Arguments> =
            TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}
