package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.model.config.GlobalConfig

import org.apache.commons.io.IOUtils
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.io.*

/**
 * @author Benjamin Alt
 */
class XmlConfigExporterTest {
    private var exporter: XmlConfigExporter? = null

    @Before
    fun setUp() {
        exporter = XmlConfigExporter()
    }

    @Test
    @Throws(Exception::class)
    fun testExportConstraintDefault() {
        val globalConfig = GlobalConfig()
        globalConfig.z3Path = "[Path to Z3 Executable]"
        globalConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        val result: ByteArrayOutputStream = exporter.export(globalConfig)
        val resultString = String(result.toByteArray(), charset("utf-8"))
        val expectedString = IOUtils.toString(
            this.javaClass.getResourceAsStream("config_valid_default.xml"), "UTF-8"
        )
        Assert.assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace(resultString))
    }
}