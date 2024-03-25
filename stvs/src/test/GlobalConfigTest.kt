package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class GlobalConfigTest {
    private var config: GlobalConfig? = null

    @Before
    @Throws(Exception::class)
    fun setUp() {
        config =
            ImporterFacade.importConfig(XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml"))
    }

    @Test
    @Throws(Exception::class)
    fun setAll() {
        val clone = GlobalConfig()
        clone.setAll(config!!)
        Assert.assertEquals(clone, config)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical: GlobalConfig = ImporterFacade.importConfig(
            XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml"),
        )
        Assert.assertEquals(identical, config)
        Assert.assertNotEquals(null, config)
        Assert.assertEquals(config, config)
        identical.windowHeight = 1000
        Assert.assertNotEquals(config, identical)
    }

    @Test
    fun testHashCode() {
        val identical: GlobalConfig = ImporterFacade.importConfig(
            XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")
        )
        Assert.assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        Assert.assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.windowHeight = 1000
        Assert.assertNotEquals(config.hashCode().toLong(), identical.hashCode().toLong())
    }
}