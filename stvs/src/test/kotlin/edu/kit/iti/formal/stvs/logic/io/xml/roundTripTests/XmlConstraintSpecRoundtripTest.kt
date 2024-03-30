package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.runners.Parameterized
import java.io.File
import java.io.IOException
import java.net.URISyntaxException

/**
 * @author Benjamin Alt
 */
class XmlConstraintSpecRoundtripTest() {
    @ParameterizedTest
    @MethodSource("testFiles")
    @Throws(URISyntaxException::class, ImportException::class, IOException::class, ExportException::class)
    fun constraintSpecRoundtripTest(file: File) {
        val fileContentsBefore = TestUtils.readFromFile(file.absolutePath)
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(file)
        val tempFile = File.createTempFile("test", "")
        ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val fileContentsAfter = TestUtils.readFromFile(tempFile.absolutePath)
        Assertions.assertEquals(
            TestUtils.removeWhitespace(fileContentsBefore),
            TestUtils.removeWhitespace(fileContentsAfter),
            "ComparisonFailure at File:" + file.path
        )
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        @Throws(URISyntaxException::class)
        fun testFiles() =
            TestUtils.getTestFiles(TestUtils.FileType.CONSTRAINT, TestUtils.Status.VALID).map { Arguments.of(it) }
    }
}
