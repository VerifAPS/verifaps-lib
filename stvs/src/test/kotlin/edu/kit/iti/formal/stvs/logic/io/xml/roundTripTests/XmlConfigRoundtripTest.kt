package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

/**
 * Created by bal on 03.03.17.
 */
class XmlConfigRoundtripTest {
    @ParameterizedTest
    @MethodSource("configFiles")
    fun configRoundtripTest(file: File) {
        val fileContentsBefore = file.reader().readText()
        val importedConfig = ImporterFacade.importConfig(file)
        val fileContentsAfter = TestUtils.stringOutputStream {
            ExporterFacade.exportConfig(importedConfig, it)
        }

        Assertions.assertEquals(
            TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter)
        )
    }

    companion object {
        @JvmStatic
        fun configFiles(): Collection<Arguments> =
            TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}
