package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.model.StvsRootModel
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlSessionExporterTest {
    private var exporter = XmlSessionExporter()

    @Test
    fun exportDefault() {
        val result = TestUtils.stringOutputStream { exporter.export(StvsRootModel(), it) }
        val expectedString = javaClass.getResourceAsStream("session_empty.xml")!!.bufferedReader().readText()
        Truth.assertThat(TestUtils.removeWhitespace(result)).isEqualTo(TestUtils.removeWhitespace(expectedString))
    }
}