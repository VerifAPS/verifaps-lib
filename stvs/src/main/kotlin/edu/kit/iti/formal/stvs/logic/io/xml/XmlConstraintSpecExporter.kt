package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.*
import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.table.*
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
        //set("comment", v.)
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
