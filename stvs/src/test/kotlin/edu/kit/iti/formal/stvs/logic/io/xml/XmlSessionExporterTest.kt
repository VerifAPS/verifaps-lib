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
    fun exportDefault() {
        val result = TestUtils.stringOutputStream { exporter.export(StvsRootModel(), it) }
        val expectedString = javaClass.getResourceAsStream("session_empty.xml")!!.bufferedReader().readText()
        Assertions.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }
}