package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.jdom2.Element
import org.jdom2.Namespace
import java.math.BigInteger

/**
 * This class provides the functionality to export a [GlobalConfig] object to an xml node.
 *
 * @author Benjamin Alt
 */
class XmlConfigExporter : XmlExporter<GlobalConfig>() {
    /**
     * Exports a given [GlobalConfig] as a XML [Node].
     *
     * @param source Global config that should be exported
     * @return The XML Node representing the global config
     * @throws ExportException Exception while marshalling
     */
    @Throws(ExportException::class)
    override fun exportToXmlNode(source: GlobalConfig): Element {
        return xml("config", NAMESPACE) {

            "general" {
                "simulationTimeout" { +BigInteger(source.simulationTimeout.toString()) }
                "verificationTimeout" { +BigInteger(source.verificationTimeout.toString()) }
                "maxLineRollout" { +BigInteger(source.maxLineRollout.toString()) }

                "windowSize" {
                    "height" { +BigInteger(source.windowHeight.toString()) }
                    "width" { +BigInteger(source.windowWidth.toString()) }
                    "maximized" { +source.windowMaximized }
                }
            }
            "editor" {
                "fontFamily" { +source.editorFontFamily }
                "fontSize" { +BigInteger(source.editorFontSize.toString()) }
            }

            "dependencies" {
                "z3Path" { +source.z3Path }
                "nuxmvFilename" { +source.nuxmvFilename }
            }
        }
    }
}

fun xml(tag: String, ns: Namespace? = NAMESPACE, function: ElementBuilder .() -> Unit): Element {
    val e = Element(tag, ns)
    ElementBuilder(e, ns).function()
    return e
}

class ElementBuilder(val e: Element, val ns: Namespace? = null) {
    operator fun String.invoke(function: ElementBuilder.() -> Unit): Element {
        val new = Element(this, ns)
        e.children.add(new)

        ElementBuilder(new, ns).function()
        return new
    }

    operator fun Any.unaryPlus(): String {
        e.text = this.toString()
        return this.toString()
    }

    fun set(name: String, valueOf: Any?) {
        if (valueOf != null) {
            e.setAttribute(name, valueOf.toString())
        }
    }

    fun append(new: Element): Element {
        e.children.add(new)
        return new
    }
}
