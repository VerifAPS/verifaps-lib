package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.NullableProperty
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintCell
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.SpecificationRow
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue

/**
 * The validator for [ConstraintSpecification]s. It converts these into the formal model:
 * [ValidSpecification]. If there are any problems while converting, then [SpecProblem]s
 * are created. This object has observable properties and can therefore be used like any other model
 * instance in the controllers.
 *
 * @author Philipp
 */
class ConstraintSpecificationValidator(
    private val typeContext: ListProperty<Type>,
    private val codeIoVariables: ListProperty<CodeIoVariable>,
    private val validFreeVariables: ObservableList<ValidFreeVariable>,
    private val specification: ConstraintSpecification
) {
    val problemsProperty = SimpleListProperty<SpecProblem>(FXCollections.observableArrayList())
    var problems: ObservableList<SpecProblem> by problemsProperty

    val validProperty: BooleanProperty = SimpleBooleanProperty(false)
    var valid: Boolean by validProperty

    val validSpecificationProperty = NullableProperty<ValidSpecification?>()
    var validSpecification: ValidSpecification? by validSpecificationProperty

    private val listenToSpecUpdate = InvalidationListener { _: Observable -> this.onSpecUpdated() }

    /**
     * Creates a validator with given observable models as context information.
     *
     * The validator observes changes in any of the given context models. It automatically updates the
     * validated specification (see [.validSpecificationProperty]) and/or the problems with
     * the constraint specification (see [.problemsProperty]).
     *
     * @param typeContext the extracted types (esp. enums) from the code area
     * @param codeIoVariables the extracted [CodeIoVariable]s from the code area
     * @param validFreeVariables the most latest validated free variables from the
     * [FreeVariableList].
     * @param specification the specification to be validated
     */
    init {
        // All these ObservableLists invoke the InvalidationListeners on deep updates
        // So if only a cell in the Specification changes, the change listener on the ObservableList
        // two layers above gets notified.
        specification.rows.addListener(listenToSpecUpdate)
        specification.durations.addListener(listenToSpecUpdate)
        specification.columnHeaders.addListener(listenToSpecUpdate)

        typeContext.addListener(listenToSpecUpdate)
        codeIoVariables.addListener(listenToSpecUpdate)
        validFreeVariables.addListener(listenToSpecUpdate)

        recalculateSpecProblems()
    }

    private fun onSpecUpdated() {
        recalculateSpecProblems()
    }


    /**
     * Calculates the problems of the specification table.
     */
    fun recalculateSpecProblems() {
        val validSpec = ValidSpecification()
        val minorSpecProblems = arrayListOf<SpecProblem>()
        val majorSpecProblems = arrayListOf<SpecProblem>()
        val typesByName = typeContext.get().associateBy { it.typeName }

        var specificationIsValid = areCellsValid(validSpec, minorSpecProblems, majorSpecProblems, typesByName)
        specificationIsValid = areDurationsValid(validSpec, majorSpecProblems) && specificationIsValid

        if (specificationIsValid) {
            validSpecification = validSpec
        } else {
            validSpecification = null
        }
        valid = specificationIsValid
    }

    /**
     * Calculates if durations are valid. Durations are never valid if the given specification is
     * invalid. Therefore `specificationIsValid == false` => `areDurationsValid(...)` ==
     * false}. Any found problem is added to `specProblems`.
     *
     * @param validSpec specification that should be checked
     * @param majorSpecProblems List of major problems
     * @param specificationIsValid does the given specification valid seem to be valid?
     * @return returns if durations are valid
     */
    private fun areDurationsValid(
        validSpec: ValidSpecification,
        majorSpecProblems: MutableList<SpecProblem>
    ): Boolean {
        var valid = true
        for (durIndex in specification.durations.indices) {
            try {
                val interval: LowerBoundedInterval = DurationParseProblem.tryParseDuration(
                    durIndex,
                    specification.durations[durIndex]!!
                )
                if (valid) {
                    validSpec.durations.add(interval)
                }
            } catch (e: SpecProblemException) {
                majorSpecProblems.add(e.problem)
                valid = false
            }
        }
        return valid
    }

    /**
     * Calculates if cells are valid. Any found problem is added to `minorSpecProblems`.
     *
     * @param validSpec specification that should be checked
     * @param minorSpecProblems List of noticeable problems
     * @param majorSpecProblems List of fatal problems
     * @param typesByName map of types found in the specification
     * @return returns if cells are valid
     */
    private fun areCellsValid(
        validSpec: ValidSpecification, minorSpecProblems: MutableList<SpecProblem>,
        majorSpecProblems: MutableList<SpecProblem>, typesByName: Map<String, Type>
    ): Boolean {
        val variableTypes =
            createVariableTypes(validSpec, minorSpecProblems, majorSpecProblems, typesByName)
        val typeChecker = TypeChecker(variableTypes)
        var specificationIsValid = true

        for (rowIndex in specification.rows.indices) {
            val row = specification.rows[rowIndex]

            val expressionsForRow = hashMapOf<String, Expression?>()

            // Check cells for problems
            for ((columnId, cell) in row!!.cells) {
                try {
                    expressionsForRow[columnId] =
                        tryValidateCellExpression(typeContext.get(), typeChecker, columnId, rowIndex, cell)
                } catch (e: SpecProblemException) {
                    majorSpecProblems.add(e.problem)
                }
            }

            specificationIsValid = majorSpecProblems.isEmpty() && specificationIsValid

            // Fixes a dumb bug with listeners getting invoked midst column adding
            if (specificationIsValid && expressionsForRow.size == validSpec.columnHeaders.size) {
                validSpec.rows.add(SpecificationRow.createUnobservableRow(expressionsForRow))
            } else {
                specificationIsValid = false
            }
        }
        return specificationIsValid
    }

    /**
     * Extracts variable types from specification. Any found problem is added to `specProblems`.
     *
     * @param validSpec specification that contains the variables
     * @param minorSpecProblems List of noticeable problems
     * @param majorSpecProblems List of fatal problems
     * @param typesByName map of types found in the specification @return returns map of variable
     * types
     */
    private fun createVariableTypes(
        validSpec: ValidSpecification,
        minorSpecProblems: MutableList<SpecProblem>, majorSpecProblems: MutableList<SpecProblem>,
        typesByName: Map<String, Type>
    ): Map<String, Type> {
        val variableTypes = validFreeVariables.associate { it.name to it.type }.toMutableMap()

        for (specIoVariable in specification.columnHeaders) {
            // Check column header for problem
            try {
                // On non-fatal problems (like missing matching CodeIoVariable)
                // minorSpecProblems::add is called:
                val validIoVariable: ValidIoVariable = InvalidIoVarProblem.tryGetValidIoVariable(
                    specIoVariable,
                    codeIoVariables.get(),
                    typesByName
                ) { e -> minorSpecProblems.add(e) }
                variableTypes[validIoVariable.name] = validIoVariable.validType
                if (majorSpecProblems.isEmpty()) {
                    validSpec.columnHeaders.add(validIoVariable)
                }
            } catch (invalidIoVarProblem: SpecProblemException) { // Fatal problem (like invalid type, etc)
                majorSpecProblems.add(invalidIoVarProblem.problem)
            }
        }
        return variableTypes
    }


    companion object {
        /**
         *
         *
         * Tries to create an [Expression]-AST from the given [ConstraintCell] that has the
         * correct type using context information (for example like a type context).
         *
         *
         * @param typeContext the type context to use for parsing the cell (needed for encountering enum
         * values)
         * @param typeChecker the type checker instance for insuring the correct type
         * @param columnId the name of the column for parsing single-sided expressions like "> 3"
         * @param row the row for better error messages
         * @param cell the cell to be validated
         * @return the AST as [Expression] that is fully type-correct.
         * @throws CellProblem if the cell could not be parsed ([CellParseProblem]) or if the cell
         * is ill-typed ([CellTypeProblem]).
         */
        @Throws(SpecProblemException::class)
        fun tryValidateCellExpression(
            typeContext: List<Type>, typeChecker: TypeChecker, columnId: String, row: Int, cell: ConstraintCell
        ): Expression {
            val expr = CellParseProblem.tryParseCellExpression(typeContext, columnId, row, cell)
            return CellTypeProblem.tryTypeCheckCellExpression(typeChecker, columnId, row, expr)
        }
    }
}
