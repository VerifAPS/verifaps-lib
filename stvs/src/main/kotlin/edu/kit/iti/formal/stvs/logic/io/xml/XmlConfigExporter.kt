/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
    override fun exportToXmlNode(source: GlobalConfig): Element = xml("config", NAMESPACE) {
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

fun xml(tag: String, ns: Namespace? = NAMESPACE, function: ElementBuilder.() -> Unit): Element {
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