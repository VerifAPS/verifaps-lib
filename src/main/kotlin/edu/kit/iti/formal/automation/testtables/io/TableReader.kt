/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.State
import edu.kit.iti.formal.automation.testtables.schema.*
import edu.kit.iti.formal.smv.ast.SMVExpr
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.w3c.dom.Element

import javax.xml.bind.JAXBContext
import javax.xml.bind.JAXBElement
import javax.xml.bind.JAXBException
import javax.xml.bind.Unmarshaller
import java.io.File
import java.util.TreeMap
import java.util.stream.Collectors

class TableReader(private val input: File) {
    val product = GeneralizedTestTable()
    private var stepNumber = 0
    private val lastColumnValue = TreeMap<Int, String>()

    @Throws(JAXBException::class)
    fun run() {
        Report.debug("read xml file %s", input)

        val jc = JAXBContext
                .newInstance(ObjectFactory::class.java)
        val jaxbUnmarshaller = jc.createUnmarshaller()
        val root = jaxbUnmarshaller
                .unmarshal(input) as JAXBElement<*>
        val xml = root.value as TestTable

        Report.debug("xml file successfully read", input)

        translateName(xml)
        translateOptions(xml)
        translateFunction(xml)
        translateVariables(xml)
        translateSteps(xml)
    }

    private fun translateName(xml: TestTable) {
        product.name = xml.name
    }

    private fun translateFunction(xml: TestTable) {
        if (xml.functions == null) {
            Report.info("No functions given in table file.")
            return
        }

        val func = xml.functions
        if (!func.isEmpty()) {
            product.addFunctions(IEC61131Facade.file(CharStreams.fromString(func)))
        }
    }

    private fun translateOptions(xml: TestTable) {
        if (xml.options == null || xml.options.option
                        .isEmpty()) {
            Report.info("No options in table file.")
            return
        }

        for (o in xml.options.option) {
            product.addOption(o.key, o.value)
            Report.info("Option %s set to %s", o.key, o.value)
        }
    }

    private fun translateSteps(xml: TestTable) {
        val r = translateSteps(xml.steps.blockOrStep)
        product.region = r
    }

    private fun translateSteps(blockOrStep: List<Any>): Region {
        val b = Block()
        b.duration = "1"
        b.stepOrBlock.addAll(blockOrStep)
        return translateSteps(b)
    }

    private fun translateSteps(steps: Block): Region {
        val r = Region(stepNumber++)
        val duration = steps.duration
        if (duration == null) {
            Report.info("Duration is not given, assume '[1,1]'")
            r.duration = Duration(1, 1)
        } else {
            r.duration = IOFacade.parseDuration(duration)
        }
        for (o in steps.stepOrBlock) {
            if (o is Step) {
                r.children.add(translateStep(o))
            } else if (o is Block) {
                r.children.add(translateSteps(o))
            }
        }
        return r
    }

    private fun translateStep(step: Step): State {
        val s = State(stepNumber++)
        val cells = step.any.stream()
                .map<Element>(Function<Any, Element> { Element::class.java.cast(it) })
                .collect<List<Element>, Any>(Collectors.toList())

        for (i in 0 until product.ioVariables.size) {
            val v = product.getIoVariables(i)
            val name = v!!.name

            var cellValue = get(cells, name)
            s.entryForColumn[name] = cellValue

            if (cellValue == null || cellValue.isEmpty()) {
                if (lastColumnValue.containsKey(i))
                    cellValue = lastColumnValue[i]
                else {
                    cellValue = DEFAULT_CELL_VALUE
                    Report.warn("No cell value for var: %s in %s/%d. Inserting '-'. ",
                            name, s.id, i)
                }
            }
            try {
                val e = IOFacade.parseCellExpression(cellValue,
                        product.getSMVVariable(name), product)
                s.add(v, e)
                lastColumnValue[i] = cellValue
            } catch (pce: ParseCancellationException) {
                Report.error("Error during parsing '%s'  for column '%s' (%d) and row '%d'", cellValue,
                        name, i, s.id)
                Report.error(pce.message)
                throw pce
            }


        }

        s.duration = IOFacade.parseDuration(step.duration)
        return s
    }

    private fun translateVariables(xml: TestTable) {
        Report.debug("%d variables found",
                xml.variables.variableOrConstraint.size)

        for (o in xml.variables.variableOrConstraint) {
            if (o is IoVariable) {
                Report.debug("\t %s : %s", o.name, o.dataType)
                product.add(o)
            }

            if (o is ConstraintVariable) {
                Report.debug("\t %s : %s", o.name, o.dataType)
                product.add(o)
            }
        }

        product.ioVariables.forEach { k, v ->
            if (v.dataType == null || v.name == null || v.name
                            .isEmpty() || v.io == null || v.io.isEmpty())
                throw IllegalArgumentException(
                        "variable $v is bad")
        }
    }

    companion object {
        private val DEFAULT_CELL_VALUE = "-"

        operator fun get(cells: List<Element>, name: String): String? {
            return cells.stream()
                    .filter { c -> c.tagName == name && c.firstChild != null }
                    .map { n -> n.firstChild.nodeValue }
                    .findFirst().orElse(null)
        }
    }

}
