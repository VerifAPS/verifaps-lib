package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.table.ConcreteCell
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import org.jdom2.Element

/**
 * This class provides the functionality to export [ ConcreteSpecifications][ConcreteSpecification] to xml nodes.
 *
 * @author Benjamin Alt
 */
class XmlConcreteSpecExporter : XmlExporter<ConcreteSpecification>() {
    private val constraintSpecExporter = XmlConstraintSpecExporter()

    /**
     * Exports a given [ConcreteSpecification] as a XML [Node].
     *
     * @param source The specification that should be exported
     * @return The XML Node representing the specification
     * @throws ExportException Exception during marshalling
     */
    @Throws(ExportException::class)
    override fun exportToXmlNode(source: ConcreteSpecification): Element = xml("specification") {
        set("isConcrete", true)
        set("isCounterExample", source.isCounterExample)
        set("name", source.name)
        append(makeVariables(source))
        append(makeRows(source))
    }


    /**
     * Build [Rows] from a [ConcreteSpecification].
     *
     * @param concreteSpec specification from which rows should be generated
     * @return rows that represent the rows of the specification
     */
    private fun makeRows(concreteSpec: ConcreteSpecification): Element = xml("rows") {
        var currentCycle = 0
        for (i in concreteSpec.durations.indices)
            "row" {
                val currentDuration = concreteSpec.durations[i].duration
                "duration" { +currentDuration.toString() }
                for (j in currentCycle until currentCycle + currentDuration)
                    "cycle" {
                        // This now corresponds to a cycle
                        for (ioVar in concreteSpec.columnHeaders)
                            "cell" {
                                val col = concreteSpec.getColumnByName(ioVar.name)
                                val cell: ConcreteCell = col.cells[j]
                                +cell.value.valueString
                            }
                    }
                currentCycle += currentDuration
            }
    }


    /**
     * Generate/Extract [Variables] from a [ConcreteSpecification].
     *
     * @param concreteSpec specification from which variables should be generated
     * @return variables that could be generated from the specification
     */
    protected fun makeVariables(concreteSpec: ConcreteSpecification): Element = xml("variables") {
        concreteSpec.columnHeaders.forEach {
            append(constraintSpecExporter.makeIoVariable(it))
        }
    }
}
