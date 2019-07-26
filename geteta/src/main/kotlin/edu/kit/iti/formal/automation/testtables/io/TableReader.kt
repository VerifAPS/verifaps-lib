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
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.schema.*
import edu.kit.iti.formal.automation.testtables.schema.ConstraintVariable
import edu.kit.iti.formal.smv.SMVType
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.w3c.dom.Element
import java.io.File
import java.util.*
import javax.xml.bind.JAXBContext
import javax.xml.bind.JAXBElement
import javax.xml.bind.JAXBException

@Deprecated("xml is not maintained for future releases")
class TableReader(private val input: File) {
    val product = GeneralizedTestTable()
    val scope = Scope.defaultScope()

    private var stepNumber = 0
    private val lastColumnValue = TreeMap<Int, String>()

    init {
        scope.types.register("ENUM", EnumerateType("ENUM", arrayListOf("a")))
        scope.types.register("BOOLEAN", AnyBit.BOOL)
    }

    @Throws(JAXBException::class)
    fun run() {
        //Report.debug("read xml file %s", input)

        val jc = JAXBContext
                .newInstance(ObjectFactory::class.java)
        val jaxbUnmarshaller = jc.createUnmarshaller()
        val root = jaxbUnmarshaller
                .unmarshal(input) as JAXBElement<*>
        val xml = root.value as TestTable

        //Report.debug("xml file successfully read", input)

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
            //Report.info("No functions given in table file.")
            return
        }

        val func = xml.functions
        if (!func.isEmpty()) {
            val elements = IEC61131Facade.file(CharStreams.fromString(func))
            elements.forEach { if (it is FunctionDeclaration) product.functions += it }
        }
    }

    private fun translateOptions(xml: TestTable) {
        if (xml.options == null || xml.options.option
                        .isEmpty()) {
            //Report.info("No options in table file.")
            return
        }

        for (o in xml.options.option) {
            product.addOption(o.key, o.value)
            //Report.info("Option %s set to %s", o.key, o.value)
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
            //Report.info("Duration is not given, assume '[1,1]'")
            r.duration = Duration.ClosedInterval(1, 1)
        } else {
            r.duration = GetetaFacade.parseDuration(duration)
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

    private fun translateStep(step: Step): TableRow {
        val s = TableRow("s%02d".format(stepNumber++))
        val cells = step.any.map { Element::class.java.cast(it) }

        for (i in 0 until product.programVariables.size) {
            val v = product.getIoVariables(i)
            val name = v.name
            val cellContent = get(cells, name, i)
            /*
            val cellValue: String =
                    if (cellContent == null || cellContent.isEmpty())
                        lastColumnValue.getOrElse(i, {
                            Report.warn("No cell value for var: %s in %s/%d. Inserting '-'. ",
                                    name, s.id, i)
                            DEFAULT_CELL_VALUE
                        })
                    else cellContent
                    */
            try {
                if (cellContent != null)
                    s.rawFields[v] = GetetaFacade.parseCell(cellContent)
                else
                    s.rawFields[v] = null

                //this.lastColumnValue[i] = cellContent
            } catch (pce: ParseCancellationException) {
                //Report.error("Error during parsing '%s'  for column '%s' (%d) and row '%d'", cellContent,
                //name, i, s.id)
                //Report.error(pce.message)
                throw pce
            }


        }
        s.duration = GetetaFacade.parseDuration(step.duration)
        return s
    }

    private fun translateVariables(xml: TestTable) {
        //Report.debug("%d variables found",
        //                xml.variables.variableOrConstraint.size)


        for (o in xml.variables.variableOrConstraint) {
            val dt = scope.resolveDataType(o.dataType.name)
            val lt: SMVType = DefaultTypeTranslator.INSTANCE.translate(dt)

            if (o is IoVariable) {
                //Report.debug("\t %s : %s", o.name, o.dataType)
                val v = edu.kit.iti.formal.automation.testtables.model.ProgramVariable(o.name,
                        dt, lt,
                        if (o.io == "input") IoVariableType.INPUT else IoVariableType.OUTPUT
                )
                product.add(v)
            }

            if (o is ConstraintVariable) {
                //Report.debug("\t %s : %s", o.name, o.dataType)
                val expr = if (o.constraint != null) {
                    GetetaFacade.parseCell(o.constraint)
                } else {
                    null
                }
                val v = edu.kit.iti.formal.automation.testtables.model.ConstraintVariable(o.name, dt, lt, expr)
                product.add(v)
            }
        }

        product.programVariables.forEach { v ->
            if (v.name.isEmpty())
                throw IllegalArgumentException(
                        "variable $v is bad")
        }
    }

    companion object {
        private const val DEFAULT_CELL_VALUE = "-"
        operator fun get(cells: List<Element>, name: String, pos: Int): String? {
            val namedCell = cells.find { it.tagName == name }
            if (namedCell != null) {
                if (namedCell.firstChild != null)
                    return namedCell.firstChild.nodeValue
            } else {
                try {
                    val indexedCell = cells.filter { it.tagName == "cell" }[pos]
                    return indexedCell.firstChild.nodeValue
                } catch (e: IndexOutOfBoundsException) {
                }
            }
            return null
        }
    }

}
