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

/**
 * Extracts the interface elements into VAR...END_VAR
 *
 * @author Alexander Weigl
 * @version 1 (20.02.18)
 */
object InterfaceBuilder : XMLTranslatorFind {
    override fun find(e: Element): Element? = when {
        e.name == "interface" -> e
        e.getChild("interface") != null -> e.getChild("interface")
        else -> null
    }

    override fun translate(e: Element, writer: CodeWriter) {
        val interfaze = find(e)
        translateVars(interfaze?.getChild("inputVars"), writer, "_INPUT")
        translateVars(interfaze?.getChild("outputVars"), writer, "_OUTPUT")
        translateVars(interfaze?.getChild("localVars"), writer)
        // TODO Test for IN_OUT and others
    }

    private fun translateVars(vars: Element?, writer: CodeWriter, suffix: String = "") {
        if (vars == null) return
        writer.nl().nl().printf("VAR$suffix").block {
            for (e in vars.getChildren("variable")) {
                val name = e.getAttributeValue("name")
                val datatype = VariableDeclXML.getDatatype(e.getChild("type"))
                val initValue = VariableDeclXML.getInitialValue(e)
                nl()
                printf("${IECXMLFacade.quoteVariable(name)} : $datatype")
                if (initValue != null) {
                    printf(" := $initValue")
                }
                printf(";")
            }
        }
        writer.nl().printf("END_VAR")
    }
}

object VariableDeclXML {
    fun getDatatype(e: Element): String {
        val derived = e.getChild("derived")
        val array = e.getChild("array")
        return when {
            derived != null -> derived.getAttributeValue("name")
            array != null -> getArray(array)
            else -> e.children[0].name
        }
    }

    fun getInitialValue(variable: Element?): String? {
        if (variable == null) {
            return null
        }
        return variable.getChild("initialValue")
            ?.getChild("simpleValue")
            ?.getAttributeValue("value")
    }

    private fun getArray(type: Element): String {
        /* <array>
                <dimension lower="0" upper="127" />
                <baseType>
                    <BYTE />
                </baseType>
           </array> */
        val lower = type.getChild("dimension").getAttributeValue("lower")
        val upper = type.getChild("dimension").getAttributeValue("upper")
        val baseType = getDatatype(type.getChild("baseType"))
        return "ARRAY[$lower..$upper] OF $baseType"
    }
}