package edu.kit.iti.formal.automation.xml

import LoadHelp
import edu.kit.iti.formal.automation.plcopenxml.FBDTranslator
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.plcopenxml.PCLOpenXMLBuilder
import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.input.SAXBuilder
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.StringWriter
import java.nio.file.Files

/**
 *
 * @author Alexander Weigl
 * @version 1 (27.02.19)
 */
object FBDTest {
    @Test
    fun read() {
        val path = LoadHelp.getResource("FBDExample.xml")
        Assumptions.assumeTrue(path != null)
        val out = IECXMLFacade.extractPLCOpenXml(path!!)
        println(out)
    }

    @Test
    fun pclOpenXmlTest() {
        val path = LoadHelp.getResource("pclopen_fbd_example.xml")
        Assumptions.assumeTrue(path != null)
        val saxBuilder = SAXBuilder()
        val element = saxBuilder.build(Files.newBufferedReader(path)).rootElement
        val sw = StringWriter()
        FBDTranslator(element, CodeWriter(sw)).run()
        println(sw)
    }
}
