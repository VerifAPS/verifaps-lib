package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.apache.commons.io.IOUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.io.*

/**
 * @author Benjamin Alt
 */
class XmlConfigExporterTest {
    private val exporter = XmlConfigExporter()

    @Test
    @Throws(Exception::class)
    fun testExportConstraintDefault() {
        val globalConfig = GlobalConfig()
        globalConfig.z3Path = "[Path to Z3 Executable]"
        globalConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        val result = TestUtils.stringOutputStream { exporter.export(globalConfig, it) }
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("config_valid_default.xml"), "UTF-8"
        )
        assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(result))
    }
}