package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
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
        Truth.assertThat(TestUtils.removeWhitespace(fileContentsAfter))
            .isEqualTo(TestUtils.removeWhitespace(fileContentsBefore))
    }

    companion object {
        @Throws(URISyntaxException::class)
        @JvmStatic
        fun testFiles() =
            TestUtils.getTestFiles(TestUtils.FileType.SESSION, TestUtils.Status.VALID)
                .map { Arguments.of(it) }
    }
}