package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import java.io.File

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecRoundtripTest() {
    @ParameterizedTest
    @MethodSource("specificationFiles")
    fun constraintSpecRoundtripTest(file: File) {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(file)
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Truth.assertThat(TestUtils.removeWhitespace(fileContentsAfter)).isEqualTo(
            TestUtils.removeWhitespace(fileContentsBefore)
        )
    }

    companion object {
        @JvmStatic
        fun specificationFiles() =
            TestUtils.getTestFiles(TestUtils.FileType.CONSTRAINT, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}
