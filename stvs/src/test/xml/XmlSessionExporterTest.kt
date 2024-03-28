package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.model.StvsRootModel

import org.apache.commons.io.FileUtils
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.io.*

/**
 * @author Benjamin Alt
 */
class XmlSessionExporterTest {
    private var exporter: XmlSessionExporter? = null

    @Before
    fun setUp() {
        exporter = XmlSessionExporter()
    }

    @Test
    @Throws(Exception::class)
    fun exportDefault() {
        val result: ByteArrayOutputStream = exporter.export(StvsRootModel())
        val resultString = String(result.toByteArray(), charset("utf-8"))
        val expectedString =
            FileUtils.readFileToString(File(this.javaClass.getResource("session_empty.xml").toURI()), "utf-8")
        Assert.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}