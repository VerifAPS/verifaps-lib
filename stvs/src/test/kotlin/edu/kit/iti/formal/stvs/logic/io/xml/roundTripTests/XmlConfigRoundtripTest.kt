package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
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

        Truth.assertThat(TestUtils.removeWhitespace(fileContentsAfter))
            .isEqualTo(TestUtils.removeWhitespace(fileContentsBefore))
    }

    companion object {
        @JvmStatic
        fun configFiles(): Collection<Arguments> =
            TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}
