package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import javafx.beans.Observable
import javafx.util.Callback

/**
 *
 *
 * A concrete instance of a specification (i.e. a specification table with cells containing only
 * concrete values and concrete durations). Counterexamples and the results of the concretization of
 * a [ConstraintSpecification] (see
 * [edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer] are of this type.
 *
 *
 * @author Benjamin Alt
 */
class ConcreteSpecification(
    name: String,
    ioVariables: MutableList<ValidIoVariable>,
    rows: MutableList<SpecificationRow<ConcreteCell>>,
    durations: MutableList<ConcreteDuration>,
    val isCounterExample: Boolean
) : SpecificationTable<ValidIoVariable, ConcreteCell, ConcreteDuration>(
    name,
    Callback<ValidIoVariable, Array<Observable>> { p: ValidIoVariable? -> arrayOf() },
    Callback<ConcreteDuration, Array<Observable>> { p: ConcreteDuration? -> arrayOf() }) {
    /**
     * Construct a new ConcreteSpecification with no rows or columns.
     *
     * @param isCounterExample True if this ConcreteSpecification is a counterexample
     */
    constructor(isCounterExample: Boolean) : this(
        ArrayList<ValidIoVariable>(),
        ArrayList<SpecificationRow<ConcreteCell>>(),
        ArrayList<ConcreteDuration>(),
        isCounterExample
    )

    /**
     * Construct a new ConcreteSpecification with given column headers, rows and durations, but with a
     * default name.
     *
     * @param ioVariables The input/output variables defining the columns
     * @param rows The rows of concrete cells. One cycle corresponds to one row
     * @param durations The concrete durations. This list can be shorter than the number of rows,
     * because for a duration of n there will be n rows.
     * @param isCounterExample True if this ConcreteSpecification is a counterexample
     */
    constructor(
        ioVariables: List<ValidIoVariable>,
        rows: List<SpecificationRow<ConcreteCell>>, durations: List<ConcreteDuration>,
        isCounterExample: Boolean
    ) : this(
        DEFAULT_NAME,
        ioVariables.toMutableList(),
        rows.toMutableList(),
        durations.toMutableList(),
        isCounterExample
    )

    /**
     * Construct a new ConcreteSpecification with given name, column headers, rows and durations.
     *
     * @param name The name of this ConcreteSpecification
     * @param ioVariables The input/output variables defining the columns
     * @param rows The rows of concrete cells. One cycle corresponds to one row
     * @param durations The concrete durations. This list can be shorter than the number of rows,
     * because for a duration of n there will be n rows.
     * @param isCounterExample True if this ConcreteSpecification is a counterexample
     */
    init {
        columnHeaders.setAll(ioVariables)
        this.rows.addAll(rows)
        this.durations.addAll(durations)
    }

    /**
     * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification: In a
     * ConcreteSpecification, a row corresponds to a cycle. One row in a ConstraintSpecification may
     * cover multiple cycles. This function returns the list of concrete values corresponding to a
     * constraint identified by its column and row (as in a ConstraintSpecification).
     *
     * @param column The column identifier for the constraint cell (the name of the input/output
     * variable)
     * @param constraintRow The row of the constraint cell (according to the ConstraintSpecification
     * row semantics, see description above)
     * @return The list of concrete cells corresponding to this concrete value
     */
    fun getConcreteValuesForConstraintCell(column: String, constraintRow: Int): List<ConcreteCell?> {
        // Counterexamples stop after first mismatch
        // So we possibly don't have as many counterexample rows as constraint rows.
        if (constraintRow >= durations.size) {
            return emptyList<ConcreteCell>()
        }
        val startIndex = durations[constraintRow].beginCycle
        val endIndex = durations[constraintRow].endCycle

        val concreteCells = ArrayList<ConcreteCell?>()
        val concreteColumn = getColumnByName(column)

        for (i in startIndex until endIndex) {
            concreteCells.add(concreteColumn.cells[i])
        }
        return concreteCells
    }

    /**
     * Returns the concrete duration for a row in a [ConstraintSpecification].
     *
     * @param constraintRow The index of a row in a [ConstraintSpecification]
     * @return The concrete duration assigned to the duration expression of the given row. The
     * Optional return value is empty if there is no such duration (e.g. in a counterexample,
     * where the error state is reached before the last row of the constraint specification)
     */
    fun getConcreteDurationForConstraintRow(constraintRow: Int): ConcreteDuration? {
        if (constraintRow >= durations.size) {
            return null
        }
        return durations[constraintRow]!!
    }

    /**
     * Maps a concrete cycle in this ConcreteSpecification to a row number in a constraint
     * specification.
     *
     * @param cycle The number of a cycle in this ConcreteSpecification
     * @return The number of the corresponding row in a ConstraintSpecification
     */
    fun cycleToRowNumber(cycle: Int): Int {
        val durationWithCycle = durations.first { duration -> isCycleInDuration(cycle, duration) }
            ?: throw IllegalArgumentException("Cycle not found")
        return durations.indexOf(durationWithCycle)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ConcreteSpecification

        if (isCounterExample != other.isCounterExample) return false
        if (name != other.name) return false
        if (rows != other.rows) return false
        if (durations != other.durations) return false
        if (columnHeaders != other.columnHeaders) return false
        return true
    }

    override fun hashCode(): Int {
        var result = isCounterExample.hashCode()
        result = 31 * result + columnHeaders.hashCode()
        result = 31 * result + name.hashCode()
        result = 31 * result + rows.hashCode()
        result = 31 * result + durations.hashCode()
        return result
    }


    companion object {
        private fun isCycleInDuration(cycle: Int, duration: ConcreteDuration): Boolean {
            return duration.beginCycle <= cycle && duration.endCycle > cycle
        }
    }
}
