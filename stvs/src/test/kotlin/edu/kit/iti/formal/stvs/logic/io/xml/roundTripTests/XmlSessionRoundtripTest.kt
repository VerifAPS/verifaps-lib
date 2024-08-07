package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import org.junit.Assert
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File
import java.io.IOException
import java.net.URISyntaxException

/**
 * @author Benjamin Alt
 */
class XmlSessionRoundtripTest() {
    @ParameterizedTest
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun sessionRoundtripTest(file: File) {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSession: StvsRootModel = ImporterFacade.importSession(file, GlobalConfig(), History())
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSession(importedSession, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assertions.assertEquals(
            TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter),
            "ComparisonFailure at file: " + file.path
        )
    }

    companion object {
        @Throws(URISyntaxException::class)
        @JvmStatic
        fun testFiles() =
            TestUtils.getTestFiles(TestUtils.FileType.SESSION, TestUtils.Status.VALID)
                .map { Arguments.of(it) }
    }
}