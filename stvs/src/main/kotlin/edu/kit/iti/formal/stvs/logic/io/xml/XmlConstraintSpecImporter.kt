package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.table.*
import org.jdom2.Element
import org.w3c.dom.Node
import java.io.IOException
import java.net.URL
import java.util.*

/**
 * This class provides the functionality to import constraint specifications from xml nodes.
 *
 * @author Benjamin Alt
 */
class XmlConstraintSpecImporter : XmlImporter<ConstraintSpecification>() {
    /**
     * Imports a [ConstraintSpecification] from a xml [Node].
     *
     * @param source Xml node that should be imported
     * @return Imported specification
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    override fun doImportFromXmlNode(source: Element): ConstraintSpecification {
        val variables = source.getChild("variables")
        val freeVariables: FreeVariableList = importFreeVariableSet(variables)
        val ioVariables: List<SpecIoVariable> = importIoVariables(variables)
        return importConstraintSpec(freeVariables, ioVariables, source)
    }

    /**
     * Imports a [ConstraintSpecification] from a [SpecificationTable].
     *
     * @param ioVariables defined variables
     * @param importedSpec specification table previously imported from xml
     * @return imported constraint specification
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    private fun importConstraintSpec(
        freeVariables: FreeVariableList,
        ioVariables: List<SpecIoVariable>,
        importedSpec: Element
    ): ConstraintSpecification {
        val constraintSpec = ConstraintSpecification(freeVariables)
        constraintSpec.name = importedSpec.getAttributeValue("name") ?: "unnamed"

        // Add the columnHeaders (column headers)
        for (specIoVariable in ioVariables) {
            constraintSpec.columnHeaders.add(specIoVariable)
        }

        // Add the rowsj
        val rows = importedSpec.getChild("rows")
        rows?.getChildren("row")?.forEach { row ->
            val duration = row.getChildText("duration")
            val newDuration = ConstraintDuration(duration)
            newDuration.comment = row.getChild("duration").getAttributeValue("comment")
            constraintSpec.durations.add(newDuration)
            val row1: SpecificationRow<ConstraintCell> = createSpecificationRowForCycle(ioVariables, row)
            constraintSpec.rows.add(row1)
        }
        constraintSpec.comment = importedSpec.getAttributeValue("comment")
        return constraintSpec
    }

    /**
     * Creates a [SpecificationRow] that represents a `row`.
     *
     * @param ioVariables IO Variables that are present in the specification
     * @param row Row which holds the information to create a specification row.
     * @return Specification row
     * @throws ImportException Mismatch between size of `row` and size of `ioVariables`
     */
    @Throws(ImportException::class)
    private fun createSpecificationRowForCycle(ioVariables: List<SpecIoVariable>, row: Element)
            : SpecificationRow<ConstraintCell> {
        val cellsMap = hashMapOf<String, ConstraintCell>()

        row.getChildren("cell").forEachIndexed { j, cell ->
            val constraintCell = ConstraintCell(cell.value)
            constraintCell.comment = cell.getAttributeValue("comment")
            cellsMap[ioVariables[j].name] = constraintCell
        }

        if (cellsMap.size != ioVariables.size) {
            throw ImportException("Row too short: Do not have a cell for each IOVariable")
        }

        val newRow = ConstraintSpecification.createRow(cellsMap)
        newRow.comment = row.getAttributeValue("comment")
        return newRow
    }

    /**
     * Imports [SpecIoVariables][SpecIoVariable] from [Variables].
     *
     * @param variables variables from which should be imported
     * @return list of specification variables
     * @throws ImportException exception while importing
     */
    @Throws(ImportException::class)
    protected fun importIoVariables(variables: Element): List<SpecIoVariable> {
        val ioVariables = arrayListOf<SpecIoVariable>()
        for (variable in variables.getChildren("ioVariable")) {
            val category =
                VariableCategory.valueOf(
                    variable.getAttributeValue("io")
                        .uppercase(Locale.getDefault())
                )
            val specIoVariable =
                SpecIoVariable(
                    category,
                    category.defaultRole,
                    variable.getAttributeValue("data-type"),
                    variable.getAttributeValue("name")
                )
            variable.getAttributeValue("colwidth")?.let {
                specIoVariable.columnConfig.width = it.toDouble()
            }
            ioVariables.add(specIoVariable)
        }
        return ioVariables
    }

    /**
     * Imports [FreeVariables][FreeVariable] from [Variables].
     *
     * @param variables variables from which should be imported
     * @return object representing the free variables
     * @throws ImportException exception while importing
     */
    @Throws(ImportException::class)
    private fun importFreeVariableSet(variables: Element): FreeVariableList {
        val freeVariableSet = arrayListOf<FreeVariable>()
        for (freeVar in variables.getChildren("freeVariable")) {
            val typeString: String = freeVar.getAttributeValue("data-type") ?: error("No data-type given")
            val name: String = freeVar.getAttributeValue("name")
            val constraint: String = freeVar.getAttributeValue("default") ?: "-"
            freeVariableSet.add(FreeVariable(name, typeString, constraint))
        }
        return FreeVariableList(freeVariableSet)
    }

    @get:Throws(IOException::class)
    override val xsdResource: URL?
        get() = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}
