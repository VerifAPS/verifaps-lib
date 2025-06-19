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
package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory

/**
 *
 * @author Alexander Weigl
 * @version 1 (22.07.18)
 */

interface XMLTranslator {
    fun isCapableOf(e: Element): Boolean
    fun translate(e: Element, writer: CodeWriter)
}

interface XMLTranslatorFind {
    fun find(e: Element): Element?
    fun isCapableOf(e: Element): Boolean = find(e) != null
    fun translate(e: Element, writer: CodeWriter)
}

abstract class XMLTranslatorXPath(protected val xpath: String) : XMLTranslator {
    companion object {
        @JvmStatic
        protected val xpathFactory = XPathFactory.instance()
    }

    val query = xpathFactory.compile(xpath, Filters.element())
    override fun isCapableOf(e: Element): Boolean = query.evaluateFirst(e) != null
}

/**
 * Translates: dataTypes/dataType with ./baseType/struct
 */
object StructTranslator : XMLTranslatorXPath("./baseType/struct") {
    override fun translate(e: Element, writer: CodeWriter) {
        val q = xpathFactory.compile("$xpath/variable", Filters.element())

        val name = e.getAttributeValue("name")
        writer.nl().printf("$name : STRUCT").increaseIndent()
        for (variable in q.evaluate(e)) {
            val n = variable.getAttributeValue("name")
            val dt = VariableDeclXML.getDatatype(variable.getChild("type"))
            val doc = variable.getChild("documentation")?.getChild("xhtml")?.textTrim
            if (doc != null) {
                writer.nl().printf("$n : $dt; (* $doc *)")
            } else {
                writer.nl().printf("$n : $dt;")
            }
        }

        writer.decreaseIndent().nl().printf("END_STRUCT;")
    }
}

/**
 * Translates: dataTypes/dataType with ./baseType/enum
 */
object EnumTranslator : XMLTranslatorXPath("./baseType/enum") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        writer.nl().printf("$name : ")
        val vq = xpathFactory.compile("$xpath/values/value/@name", Filters.attribute())
        val values = vq.evaluate(e)
        values.joinTo(writer, ", ", "(", ");") { it.value }
    }
}