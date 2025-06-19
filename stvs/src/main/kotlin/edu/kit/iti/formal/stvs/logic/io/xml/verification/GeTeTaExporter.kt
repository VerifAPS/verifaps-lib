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
package edu.kit.iti.formal.stvs.logic.io.xml.verification

import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.jdom2.Element

/**
 * Exporter for communication with the GeTeTa verification engine. Provides functionality for
 * converting [ConstraintSpecification]s into an XML format compatible with the GeTeTa input
 * format.
 *
 * @author Benjamin Alt
 */
class GeTeTaExporter : XmlExporter<ConstraintSpecification>() {
    //    /**
//     * Creates [Steps] that correspond to the rows in the given [ConstraintSpecification].
//     *
//     * @param source The specification for which the steps should be generated
//     * @return Steps object (to be inserted into a [TestTable])
//     */
//    private fun makeSteps(source: ConstraintSpecification): Steps {
//        val steps: Steps = objectFactory.createSteps()
//        // A step corresponds to a row in a ConstraintSpecification
//        val rows: List<SpecificationRow<ConstraintCell>> = source.rows
//        val durations: List<ConstraintDuration> = source.durations
//        for (i in rows.indices) {
//            val row: SpecificationRow<ConstraintCell> = rows[i]
//            val step: Step = objectFactory.createStep()
//            step.setDuration(durations[i].asString)
//            for (specIoVariable in source.columnHeaders) {
//                val variable: String = specIoVariable.name
//                val cell: ConstraintCell = row.cells.get(variable)
//                step.getCell().add(VariableEscaper.escapeCellExpression(cell.asString))
//            }
//            steps.getBlockOrStep().add(step)
//        }
//        return steps
//    }
//
//    /**
//     * Creates [Variables] from all free and i/o variables present in the given
//     * [ConstraintSpecification].
//     *
//     * @param source The specification from which the variables should be taken
//     * @return Variables object ready to be used in a [TestTable]
//     */
//    private fun makeVariables(source: ConstraintSpecification): Variables {
//        val variables: Variables = objectFactory.createVariables()
//        variables.getVariableOrConstraint().addAll(makeIoVariables(source).getVariableOrConstraint())
//        variables.getVariableOrConstraint().addAll(makeFreeVariables(source).getVariableOrConstraint())
//        return variables
//    }
//
//    /**
//     * Creates [Variables] from the [FreeVariables][FreeVariable] present in the given
//     * [ConstraintSpecification].
//     *
//     * @param source The specification from which the variables should be generated
//     * @return Variables object
//     */
//    private fun makeFreeVariables(source: ConstraintSpecification): Variables {
//        val variables: Variables = objectFactory.createVariables()
//        for (freeVariable in source.freeVariableList.variables) {
//            val exportedVariable: ConstraintVariable = objectFactory.createConstraintVariable()
//            exportedVariable.setName(VariableEscaper.escapeIdentifier(freeVariable.name))
//            exportedVariable.setDataType(getDataType(freeVariable))
//            if (freeVariable.constraint.length > 0) {
//                exportedVariable
//                    .setConstraint(VariableEscaper.escapeIdentifier(freeVariable.constraint))
//            } else {
//                exportedVariable.setConstraint("-")
//            }
//            variables.getVariableOrConstraint().add(exportedVariable)
//        }
//        return variables
//    }
//
//    /**
//     * Creates [Variables] from the [SpecIoVariable] present in the given
//     * [ConstraintSpecification].
//     *
//     * @param source The specification from which the variables should be taken
//     * @return Variables object
//     */
//    private fun makeIoVariables(source: ConstraintSpecification): Variables {
//        val variables: Variables = objectFactory.createVariables()
//        for (ioVariable in source.columnHeaders) {
//            val exportedVariable: IoVariable = objectFactory.createIoVariable()
//            exportedVariable.setName(VariableEscaper.escapeIdentifier(ioVariable.name))
//            exportedVariable.setDataType(getDataType(ioVariable))
//            if (ioVariable.role == VariableRole.ASSERT) {
//                exportedVariable.setIo("output")
//            } else {
//                exportedVariable.setIo("input")
//            }
//            variables.getVariableOrConstraint().add(exportedVariable)
//        }
//        return variables
//    }
//
//    /**
//     * Create the [DataType] for a given variable.
//     *
//     * @param variable Variable from which the @link DataType} should be determined
//     * @return the determined @link DataType} of the `variable`
//     */
//    private fun getDataType(variable: Variable): DataType {
//        return if (variable.type == "INT") {
//            DataType.INT
//        } else if (variable.type == "BOOL") {
//            DataType.BOOLEAN
//        } else {
//            DataType.ENUM
//        }
//    }
//
//    /**
//     * Converts a given [ConstraintSpecification] into an XML node that conforms to the GeTeTa
//     * verification engine input format.
//     *
//     * @param source The specification that should be converted
//     * @return XML Node representing the specification
//     * @throws ExportException if marshalling was not successful
//     */
//    @Throws(ExportException::class)
//    override fun exportToXmlNode(source: ConstraintSpecification): Node {
//        val testTable: TestTable = objectFactory.createTestTable()
//        testTable.setVariables(makeVariables(source))
//        testTable.setSteps(makeSteps(source))
//        val element: JAXBElement<TestTable> = objectFactory.createTestTable(testTable)
//        return XmlExporter.Companion.marshalToNode(element, XmlExporter.Companion.OF_EXTETA)
//    }
//
//    companion object {
//        private const val EXTETA_NAMESPACE = "edu.kit.iti.formal.exteta_1"
//    }
    override fun exportToXmlNode(source: ConstraintSpecification): Element {
        TODO("Not yet implemented")
    }
}