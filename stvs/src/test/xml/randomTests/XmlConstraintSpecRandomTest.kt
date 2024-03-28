package edu.kit.iti.formal.stvs.logic.io.xml.randomTests

import edu.kit.iti.formal.stvs.RandomTest
import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.logic.io.xml.RandomTableGenerator
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import junit.framework.TestCase
import org.apache.commons.io.FileUtils
import org.junit.Before
import org.junit.jupiter.api.Test
import org.junit.experimental.categories.Category
import java.io.File
import java.io.IOException

/**
 * Created by bal on 02.03.17.
 */
@Category(RandomTest::class)
class XmlConstraintSpecRandomTest {
    private val MAX_COLUMNS = 100
    private val MAX_ROWS = 100
    private val MAX_FREE_VARIABLES = 3
    private var generator: RandomTableGenerator? = null

    @Before
    fun setUp() {
        generator = RandomTableGenerator(100)
    }

    @Test
    @Throws(IOException::class, ExportException::class, ImportException::class)
    fun testRandomAll() {
        var columns = 1
        while (columns <= MAX_COLUMNS) {
            var rows = 0
            while (rows <= MAX_ROWS) {
                for (freeVariables in 0..MAX_FREE_VARIABLES) {
                    System.out.format("Testing random %d %d %d %n", columns, rows, freeVariables)
                    testRandom(columns, rows, freeVariables)
                }
                rows += 10
            }
            columns += 10
        }
    }

    @Throws(IOException::class, ExportException::class, ImportException::class)
    private fun testRandom(columns: Int, rows: Int, freeVariables: Int) {
        val tempFile = File.createTempFile("randomTest", "")
        val originalSpec = generator!!.randomConstraintSpec(
            columns, rows,
            freeVariables
        )
        ExporterFacade.exportSpec(originalSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val originalFileContents = FileUtils.readFileToString(tempFile, "utf-8")
        val importedSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            tempFile,
            ImporterFacade.ImportFormat.XML
        )
        TestCase.assertEquals(originalSpec, importedSpec)
        ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile)
        val reexportedFileContents = FileUtils.readFileToString(tempFile, "utf-8")
        TestCase.assertEquals(originalFileContents, reexportedFileContents)
    }

    private fun testRandomModelToModel(columns: Int, rows: Int, freeVariables: Int) {
    }
}
