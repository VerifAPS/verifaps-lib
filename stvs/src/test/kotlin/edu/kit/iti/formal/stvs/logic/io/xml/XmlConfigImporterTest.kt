package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class XmlConfigImporterTest {
    private var importer = XmlConfigImporter()

    @Test
    fun testDoImport() {
        val inputStream = XmlConfigImporter::class.java.getResourceAsStream("config_valid_nodeps.xml")!!
        val config: GlobalConfig = importer.doImport(inputStream)
        Assertions.assertEquals("EN", config.uiLanguage)
        Assertions.assertEquals(100, config.verificationTimeout)
        Assertions.assertEquals(100, config.simulationTimeout)
        Assertions.assertEquals("Comic Sans", config.editorFontFamily)
        Assertions.assertEquals(12, config.editorFontSize.toLong())
        Assertions.assertEquals(true, config.showLineNumbers)
    }

    @Test
    fun testDoImportDefault() {
        val inputStream =
            javaClass.getResourceAsStream("/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default.xml")!!
        val actualConfig: GlobalConfig = importer.doImport(inputStream)
        val expectedConfig = GlobalConfig()
        expectedConfig.z3Path = "[Path to Z3 Executable]"
        expectedConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        Assertions.assertEquals(expectedConfig, actualConfig)
    }

    @Test
    fun testDoImportInvalidData() {
        assertFailsWith<ImportException> {
            val inputStream = this.javaClass.getResourceAsStream("config_invalid_1.xml")!!
            importer.doImport(inputStream)
        }
    }
}