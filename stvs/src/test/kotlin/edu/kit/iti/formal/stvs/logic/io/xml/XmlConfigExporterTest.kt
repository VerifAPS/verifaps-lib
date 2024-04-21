package edu.kit.iti.formal.stvs.logic.io.xml

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 */
class XmlConfigExporterTest {
    private val exporter = XmlConfigExporter()

    @Test
    fun testExportConstraintDefault() {
        val globalConfig = GlobalConfig()
        globalConfig.z3Path = "[Path to Z3 Executable]"
        globalConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        val act = TestUtils.stringOutputStream { exporter.export(globalConfig, it) }
        val exp = javaClass.getResourceAsStream("config_valid_default.xml")!!.bufferedReader().readText()
        Truth.assertThat(
            TestUtils.removeWhitespace(act)
        ).isEqualTo(TestUtils.removeWhitespace(exp))
    }
}