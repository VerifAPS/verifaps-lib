package edu.kit.iti.formal.automation.xml

import LoadHelp
import edu.kit.iti.formal.automation.plcopenxml.FBDTranslator
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.plcopenxml.PCLOpenXMLBuilder
import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.filter.Filters
import org.jdom2.input.SAXBuilder
import org.jdom2.xpath.XPathFactory
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
    fun fbdExampleDotFile() {
        val path = LoadHelp.getResource("FBDExample.xml")
        Assumptions.assumeTrue(path != null)
        val saxBuilder = SAXBuilder()
        saxBuilder.saxHandlerFactory = PCLOpenXMLBuilder.FACTORY
        val doc = saxBuilder.build(path?.toUri()?.toURL())
        val xpathFactory = XPathFactory.instance()
        val pou = xpathFactory.compile("//pou[@name=\"FBD1\"]/body/FBD", Filters.element()).evaluateFirst(doc)
        Assumptions.assumeTrue(pou != null)

        val t = FBDTranslator(pou, CodeWriter())
        val body = t.generateFbdBody()
        val c = CodeWriter()
        body.writeDot(c)
        body.asStructuredText(c)
        println(c.stream.toString())
    }


    @Test
    fun fbdExample() {
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
