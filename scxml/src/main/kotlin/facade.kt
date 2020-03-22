import org.jdom2.Document
import org.jdom2.input.SAXBuilder
import org.jdom2.input.sax.SAXHandler
import org.jdom2.input.sax.SAXHandlerFactory
import org.jdom2.xpath.XPathFactory
import org.xml.sax.Attributes
import org.xml.sax.InputSource
import java.io.File
import java.io.Reader
import java.nio.file.Files
import java.nio.file.Path

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/22/20)
 */
object ScXmlFacade {
    fun read(file: Reader): Document {
        val saxBuilder = createSaxBuilder()
        return saxBuilder.build(InputSource(file))
    }


    fun read(file: File) = SCXml(createSaxBuilder().build(file))
    fun read(file: Path) = Files.newBufferedReader(file).use { SCXml(read(it)) }


    private fun createSaxBuilder(): SAXBuilder {
        val saxBuilder = SAXBuilder()
        saxBuilder.saxHandlerFactory = FACTORY
        return saxBuilder
    }

    private val FACTORY = SAXHandlerFactory {
        object : SAXHandler() {
            override fun startElement(
                    namespaceURI: String?, localName: String?, qName: String?, atts: Attributes?) {
                super.startElement("", localName, qName, atts)
            }

            override fun startPrefixMapping(prefix: String?, uri: String?) {}
        }
    }
    private val xpathFactory = XPathFactory.instance()

}