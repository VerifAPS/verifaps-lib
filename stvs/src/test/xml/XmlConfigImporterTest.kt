package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.config.GlobalConfig

import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test
import java.io.File
import java.io.FileInputStream

/**
 * @author Benjamin Alt
 */
class XmlConfigImporterTest {
    private var importer: XmlConfigImporter? = null

    @Before
    fun setUp() {
        importer = XmlConfigImporter()
    }

    @Test
    @Throws(Exception::class)
    fun testDoImport() {
        val inputStream: FileInputStream =
            FileInputStream(File(XmlConfigImporter::class.java.getResource("config_valid_nodeps.xml").toURI()))
        val config: GlobalConfig = importer.doImport(inputStream)
        Assert.assertEquals("EN", config.uiLanguage)
        Assert.assertEquals(100, config.verificationTimeout.toLong())
        Assert.assertEquals(100, config.simulationTimeout.toLong())
        Assert.assertEquals("Comic Sans", config.editorFontFamily)
        Assert.assertEquals(12, config.editorFontSize.toLong())
        Assert.assertEquals(true, config.showLineNumbers)
    }

    @Test
    @Throws(Exception::class)
    fun testDoImportDefault() {
        val inputStream = FileInputStream(
            File(
                this.javaClass.getResource(
                    "/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
                            ".xml"
                ).toURI()
            )
        )
        val actualConfig: GlobalConfig = importer.doImport(inputStream)
        val expectedConfig = GlobalConfig()
        expectedConfig.z3Path = "[Path to Z3 Executable]"
        expectedConfig.nuxmvFilename = "[Path to NuXmv Executable]"
        Assert.assertEquals(expectedConfig, actualConfig)
    }

    @Test(expected = ImportException::class)
    @Throws(Exception::class)
    fun testDoImportInvalidData() {
        val inputStream = FileInputStream(File(this.javaClass.getResource("config_invalid_1.xml").toURI()))
        val config: GlobalConfig = importer.doImport(inputStream)
    }
}