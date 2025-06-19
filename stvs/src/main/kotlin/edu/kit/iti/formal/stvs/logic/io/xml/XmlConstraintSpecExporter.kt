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
import edu.kit.iti.formal.stvs.model.common.IoVariable
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.jdom2.Element

/**
 * This class provides the functionality to export [ ConstraintSpecifications][ConstraintSpecification] to xml nodes.
 *
 * @author Benjamin Alt
 */
class XmlConstraintSpecExporter : XmlExporter<ConstraintSpecification>() {
    /**
     * Exports a given [ConstraintSpecification] as a XML [Node].
     *
     * @param source The specification that should be exported
     * @return The XML Node representing the specification
     * @throws ExportException Exception during marshalling
     */
    @Throws(ExportException::class)
    override fun exportToXmlNode(source: ConstraintSpecification): Element = xml("specification") {
        append(makeVariables(source))
        append(makeRows(source))
        set("comment", source.comment)
        set("isConcrete", false)
        set("name", source.name)
    }

    /**
     * Build [Rows] from a [ConcreteSpecification].
     *
     * @param constraintSpec specification from which rows should be generated
     * @return rows that represent the rows of the specification
     */
    private fun makeRows(constraintSpec: ConstraintSpecification) = xml("rows") {
        constraintSpec.rows.forEachIndexed { i, row ->
            "row" {
                set("comment", row.comment)
                "duration" {
                    +(constraintSpec.durations[i].asString ?: "")
                    set("comment", constraintSpec.durations[i].comment)
                }

                constraintSpec.columnHeaders.forEach { v ->
                    row.cells[v.name]?.let { cell ->
                        "cell" {
                            set("comemnt", cell.comment)
                            +(cell.asString ?: "")
                        }
                    }
                }
            }
        }
    }

    /**
     * Generate/Extract [Variables] from a [ConstraintSpecification].
     *
     * @param constraintSpec specification from which variables should be generated
     * @return variables that could be generated from the specification
     */
    private fun makeVariables(constraintSpec: ConstraintSpecification): Element = xml("variables") {
        constraintSpec.columnHeaders.forEach {
            append(makeIoVariablesFromSpec(it))
        }

        constraintSpec.freeVariableList.variables.forEach {
            "freeVariable" {
                set("name", it.name)
                set("data-type", it.type)
                set("default", it.constraint)
            }
        }
    }

    /**
     * Create a [Variables.IoVariable] from a [IoVariable].
     *
     * @param validIoVariable Variable from which a [Variables.IoVariable] should be generated
     * @return generated [Variables.IoVariable]
     */
    fun makeIoVariable(v: IoVariable): Element = xml("ioVariable") {
        // set("comment", v.)
        set("data-type", v.type)
        set("io", v.category.toString().lowercase())
        set("name", v.name)
    }

    /**
     * Generate a [Variables.IoVariable] from a [SpecIoVariable].
     *
     * @param specIoVariable variable to be coverted
     * @return converted variable
     */
    protected fun makeIoVariablesFromSpec(specIoVariable: SpecIoVariable): Element {
        val ioVar = makeIoVariable(specIoVariable)
        ioVar.setAttribute("colwidth", specIoVariable.columnConfig.width.toString())
        return ioVar
    }
}