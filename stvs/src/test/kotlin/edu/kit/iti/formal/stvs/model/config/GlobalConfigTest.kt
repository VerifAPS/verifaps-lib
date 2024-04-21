package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class GlobalConfigTest {
    private var config: GlobalConfig =
        ImporterFacade.importConfig(XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!)

    @Test
    @Throws(Exception::class)
    fun setAll() {
        val clone = GlobalConfig()
        clone.setAll(config)
        Assertions.assertEquals(clone, config)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical: GlobalConfig =
            ImporterFacade.importConfig(XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!)
        Assertions.assertEquals(identical, config)
        Assertions.assertNotEquals(null, config)
        Assertions.assertEquals(config, config)
        identical.windowHeight = 1000
        Assertions.assertNotEquals(config, identical)
    }

    @Test
    fun testHashCode() {
        val identical: GlobalConfig = ImporterFacade.importConfig(
            XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!
        )
        Assertions.assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        Assertions.assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.windowHeight = 1000
        Assertions.assertNotEquals(config.hashCode().toLong(), identical.hashCode().toLong())
    }
}