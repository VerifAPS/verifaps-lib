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

class PouExtractor(
    val pous: List<Element>,
    val writer: CodeWriter,
    val translators: List<XMLTranslator> =
        listOf<XMLTranslator>(FunctionTranslator, FunctionBlockTranslator, ProgramTranslator),
) {
    fun run() {
        val p = pous.sortedWith(compareBy({ it.getAttributeValue("pouType") }, { it.getAttributeValue("name") }))
        p.forEach { pou -> run(pou) }
    }

    fun run(pou: Element) {
        translators.forEach { t ->
            if (t.isCapableOf(pou)) {
                t.translate(pou, writer)
                writer.nl().nl().nl()
                return
            }
        }
    }
}

object Actions : XMLTranslatorXPath("./actions") {
    override fun translate(e: Element, writer: CodeWriter) {
        val actions = xpathFactory.compile("$xpath/action", Filters.element())
        actions.evaluate(e).forEach {
            Action.translate(it, writer)
        }
    }
}

object Action : XMLTranslator {
    override fun isCapableOf(e: Element): Boolean = e.name == "action"
    override fun translate(e: Element, writer: CodeWriter) {
        writer.nl().printf("ACTION ${e.getAttributeValue("name")}").increaseIndent()
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        writer.decreaseIndent().nl().printf("END_ACTION")
    }
}

abstract class POUTranslator(val type: String) : XMLTranslator {
    override fun isCapableOf(e: Element): Boolean = e.getAttributeValue("pouType") == type
}

object FunctionTranslator : POUTranslator("function") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        val returnType = VariableDeclXML.getDatatype(e.getChild("interface").getChild("returnType"))
        writer.printf("FUNCTION $name : $returnType")
            .increaseIndent().nl()
        InterfaceBuilder.translate(e, writer)
        STBody.translate(e, writer)
        FBDBody.translate(e, writer)
        writer.decreaseIndent().nl().printf("END_FUNCTION")
    }
}

object FunctionBlockTranslator : POUTranslator("functionBlock") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        writer.printf("FUNCTION_BLOCK $name").increaseIndent().nl()

        InterfaceBuilder.translate(e, writer)
        Actions.translate(e, writer)
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        FBDBody.translate(e, writer)

        writer.decreaseIndent().nl().printf("END_FUNCTION_BLOCK").nl()
    }
}

object ProgramTranslator : POUTranslator("program") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = (e.getAttributeValue("name"))
        writer.printf("PROGRAM $name").increaseIndent().nl()

        InterfaceBuilder.translate(e, writer)
        Actions.translate(e, writer)
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        FBDBody.translate(e, writer)

        writer.decreaseIndent().nl().printf("END_PROGRAM").nl()
    }
}

object SFCBody : XMLTranslatorXPath("./body/SFC") {
    override fun translate(e: Element, writer: CodeWriter) {
        val getSTBody = xpathFactory.compile("./body/SFC", Filters.element())
        val sfcElement = getSTBody.evaluateFirst(e)
        if (sfcElement != null) {
            SFCFactory(sfcElement, writer).run()
        }
    }
}

object STBody : XMLTranslatorXPath("./body/ST/xhtml") {
    override fun translate(e: Element, writer: CodeWriter) {
        val stBody = query.evaluateFirst(e)
        if (stBody != null) {
            val body = stBody.textTrim
            val body2 = IECXMLFacade.quoteStBody(body)
            writer.nl().appendReformat(body2)
        }
    }
}

object FBDBody : XMLTranslatorXPath("./body/FBD") {
    override fun translate(e: Element, writer: CodeWriter) {
        val fbd = query.evaluateFirst(e)
        if (fbd != null) {
            FBDTranslator(fbd, writer).run()
        }
    }
}