package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.model.StvsRootModel
import org.apache.commons.io.FileUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.*

/**
 * @author Benjamin Alt
 */
class XmlSessionExporterTest {
    private var exporter = XmlSessionExporter()

    @Test
    @Throws(Exception::class)
    fun exportDefault() {
        val result = TestUtils.stringOutputStream { exporter.export(StvsRootModel(), it) }
        val resultString = String(result.toByteArray(), charset("utf-8"))
        val expectedString =
            FileUtils.readFileToString(File(this.javaClass.getResource("session_empty.xml")!!.toURI()), "utf-8")
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}