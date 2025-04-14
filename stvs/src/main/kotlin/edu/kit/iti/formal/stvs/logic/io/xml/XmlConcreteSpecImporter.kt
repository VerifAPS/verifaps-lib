package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.common.VariableRole
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.Value
import edu.kit.iti.formal.stvs.model.table.*
import org.jdom2.Element
import java.io.IOException
import java.net.URL
import java.util.*

/**
 * This class provides the functionality to import concrete specifications from xml nodes.
 *
 * @author Benjamin Alt
 */
class XmlConcreteSpecImporter(private val typeContext: List<Type>) : XmlImporter<ConcreteSpecification>() {
    /**
     * Imports a [ConcreteSpecification] from a xml [Node].
     *
     * @param source Xml node that should be imported
     * @return Imported specification
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    override fun doImportFromXmlNode(source: Element): ConcreteSpecification {
        val validIoVariables = importIoVariables(source.getChild("variables"))
        return importConcreteSpec(validIoVariables, source)
    }

    /**
     * Imports [ValidIoVariables][ValidIoVariable] from [Variables] under use of the
     * previously specified `typeContext`.
     *
     * @param variables variables from which should be imported
     * @return list of valid variables
     * @throws ImportException exception while importing
     */
    @Throws(ImportException::class)
    private fun importIoVariables(variables: Element): List<ValidIoVariable> {
        return variables.getChildren("ioVariable").map { variable ->
            val category = VariableCategory.valueOf(variable.getAttributeValue("io").uppercase(Locale.getDefault()))
            val dt = variable.getAttributeValue("data-type")
            val type = typeContext.find { t: Type -> t.typeName == dt } ?: error("Unknown variable type: $dt")
            val name = variable.getAttributeValue("name")
            variable.getAttributeValue("role")
                ?.let { v -> VariableRole.entries.firstOrNull { it.name == v } }
                ?: category.defaultRole
            ValidIoVariable(category, name, type, category.defaultRole)
        }
    }


    /**
     * Imports a [ConcreteSpecification] from a [SpecificationTable].
     *
     * @param ioVariables defined variables
     * @param importedSpec specification table previously imported from xml
     * @return imported concrete specification
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    private fun importConcreteSpec(ioVariables: List<ValidIoVariable>, importedSpec: Element)
            : ConcreteSpecification {
        val concrete = importedSpec.getAttributeValue("isConcrete").toBoolean()
        val counterExample = importedSpec.getAttributeValue("isCounterExample").toBoolean()
        if (!concrete) {
            throw ImportException(
                "Cannot import a ConcreteSpecification from a specification not "
                        + "declared as concrete"
            )
        }
        val concreteSpec = ConcreteSpecification(counterExample)
        concreteSpec.name = importedSpec.getAttributeValue("name")

        // Add the column headers
        concreteSpec.columnHeaders.addAll(ioVariables)

        // Add the rows
        val rows = importedSpec.getChild("rows")
        var currentCycle = 0
        rows.getChildren("row").forEach { row ->
            val currentDuration = row.getChild("duration").text.toInt()
            concreteSpec.durations.add(ConcreteDuration(currentCycle, currentDuration))
            row.getChildren("cycle").forEachIndexed { j, cycle ->
                concreteSpec.rows.add(createSpecificationRowForCycle(ioVariables, row, cycle, j))
            }
            currentCycle += currentDuration
        }
        return concreteSpec
    }

    /**
     * Creates a row that represents a single cycle within a `row`. Note that one `row`
     * can map to multiple [SpecificationRows][SpecificationRow] and this method only creates the
     * row with the specified `cycleNum`.
     *
     * @param ioVariables IO Variables that are present in the specification
     * @param row Row which holds the information to create a specification row.
     * @param cycleNum Number of the cycle for which a row should be created
     * @return Specification row for one cycle
     * @throws ImportException Mismatch between size of `row` and size of `ioVariables`
     */
    @Throws(ImportException::class)
    private fun createSpecificationRowForCycle(
        ioVariables: List<ValidIoVariable>,
        row: Element,
        cycle: Element,
        cycleNum: Int
    )
            : SpecificationRow<ConcreteCell> {
        val cellsMap = hashMapOf<String, ConcreteCell>()
        val cells = cycle.getChildren("cell")
        if (cells.size != ioVariables.size) {
            throw ImportException("Row too short: Do not have a cell for each IOVariable")
        }
        cells.zip(ioVariables).forEach { (cell, variable) ->
            val v: Value = variable?.validType?.parseLiteral(cell.text) ?: error("Illegal value literal: $cell")
            val concreteCell = ConcreteCell(v)
            cellsMap[variable.name] = concreteCell
        }
        return SpecificationRow.createUnobservableRow(cellsMap)
    }

    @get:Throws(IOException::class)
    override val xsdResource: URL?
        get() = this.javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}
