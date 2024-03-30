package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.common.*
import javafx.beans.Observable
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue
import java.util.*

/**
 * A [ConstraintSpecification] which also has an associated counterexample (a
 * [ConcreteSpecification]), a concrete instance ([ConcreteSpecification]) or both. This
 * class is the model on which the [edu.kit.iti.formal.stvs.view.spec.SpecificationController]
 * and [TimingDiagramCollectionController] operate.
 *
 * @author Benjamin Alt
 */
class HybridSpecification(name: String, freeVariableList: FreeVariableList, val isEditable: Boolean) :
    ConstraintSpecification(name, freeVariableList) {
    val counterExampleProperty = NullableProperty<ConcreteSpecification?>()
    var counterExample: ConcreteSpecification?
        get() = counterExampleProperty.get()
        /**
         * Sets the counterexample for this hybrid specification. This will automatically update
         * the [HybridRow]'s counterexample cells in [.getHybridRows] from the given
         * counterexample.
         *
         * @param counterExample the concrete specification to be shown in-place in the gui
         * @throws IllegalArgumentException if the given concrete instance's column headers don't match
         * this specification's column headers
         */
        set(value) {
            if (value != null) {
                require(columnHeadersMatch(value.columnHeaders)) {
                    ("The column headers of the concrete instance are not "
                            + "compatible with this hybrid specification")
                }
            }
            this.counterExampleProperty.set(value)
        }

    val concreteInstanceProperty = NullableProperty<ConcreteSpecification?>()
    var concreteInstance: ConcreteSpecification?
        get() = concreteInstanceProperty.get()
        /**
         *
         * Set the generated concrete instance for this hybrid specification, that is the
         * concretized constraint specification. This is concrete instance is then used from
         * the [TimingDiagramCollectionController] to view a timing diagram.
         *
         * @param concreteInstance the concretized constraint specification
         * @throws IllegalArgumentException if the given concrete instance's column headers don't match
         * this specification's column headers
         */
        set(value) {
            if (value != null) {
                require(columnHeadersMatch(value.columnHeaders)) {
                    ("The column headers of the concrete instance are not "
                            + "compatible with this hybrid specification")
                }
            }
            this.concreteInstanceProperty.set(value)
        }

    val hybridRowsProperty = SimpleListProperty<HybridRow>(FXCollections.observableArrayList())
    var hybridRows: ObservableList<HybridRow> by hybridRowsProperty

    /**
     * Stores which cell in the table is currently highlighted in the view. This is saved here in
     * order to allow the table and timing diagram to share the same reference.
     */
    private val selection = Selection()

    /**
     * Create a new, empty hybrid specification with a default name from a list of free variables.
     *
     * @param freeVariableList A list of initial free variables
     * @param editable True if this hybridSpecification is editable, false otherwise
     */
    constructor(
        freeVariableList: FreeVariableList,
        editable: Boolean
    ) : this(DEFAULT_NAME, freeVariableList, editable)

    /**
     * Create a new, empty hybrid specification with a given name and a list of free variables.
     */
    init {
        hybridRowsProperty.addListener(ListChangeListener<HybridRow> { change ->
            this.onHybridRowChanged(change)
        })
        counterExampleProperty.addListener { event: Observable? -> onCounterExampleChanged() }
    }

    /**
     * Create a HybridSpecification from a [ConstraintSpecification].
     *
     * @param sourceSpec The original [ConstraintSpecification]
     * @param editable True if this HybridSpecification is editable, false otherwise
     */
    constructor(sourceSpec: ConstraintSpecification, editable: Boolean) : this(
        sourceSpec.name,
        sourceSpec.freeVariableList,
        editable
    ) {
        columnHeaders.addAll(sourceSpec.columnHeaders)

        for (rowIndex in sourceSpec.rows.indices) {
            val row = HybridRow(
                sourceSpec.rows[rowIndex],
                sourceSpec.durations[rowIndex]
            )
            row.updateCounterExampleCells(rowIndex, counterExample)
            hybridRowsProperty.add(row)
        }
    }

    private fun onCounterExampleChanged() {
        for (rowIndex in rows.indices) {
            hybridRowsProperty[rowIndex]!!.updateCounterExampleCells(rowIndex, counterExample)
        }
    }

    private fun onHybridRowChanged(change: ListChangeListener.Change<out HybridRow>) {
        while (change.next()) {
            if (change.wasAdded()) {
                val rowsToBeAdded = arrayListOf<SpecificationRow<ConstraintCell>>()
                val durationsToBeAdded: MutableList<ConstraintDuration?> = ArrayList()
                for (row in change.addedSubList) {
                    val rowToBeAdded = row.sourceRow
                    rowToBeAdded.commentProperty.bindBidirectional(row!!.commentProperty)
                    rowsToBeAdded.add(rowToBeAdded)
                    durationsToBeAdded.add(row.duration.cell!!)
                }
                rows.addAll(change.from, rowsToBeAdded)
                durations.addAll(change.from, durationsToBeAdded)
            }
            if (change.wasRemoved()) {
                rows.remove(change.from, change.from + change.removedSize)
                durations.remove(change.from, change.from + change.removedSize)
            }
        }
    }


    fun getSelection(): Selection = selection


    private fun columnHeadersMatch(columnHeaders: ObservableList<ValidIoVariable>): Boolean {
        if (this.columnHeaders.size != columnHeaders.size) {
            return false
        }
        for (i in this.columnHeaders.indices) {
            if (!this.columnHeaders[i]!!.matches(columnHeaders[i]!!)) {
                return false
            }
        }
        return true
    }

    fun removeConcreteInstance() {
        concreteInstanceProperty.set(null)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false
        if (!super.equals(other)) return false

        other as HybridSpecification

        if (isEditable != other.isEditable) return false
        if (counterExample != other.counterExample) return false
        if (concreteInstance != other.concreteInstance) return false
        if (hybridRows != other.hybridRows) return false
        if (selection != other.selection) return false
        if (columnHeaders != other.columnHeaders) return false
        if (comment != other.comment) return false
        if (rows != other.rows) return false
        if (freeVariableList != other.freeVariableList) return false
        if (durations != other.durations) return false
        if (name != other.name) return false
        if (concreteInstance != other.concreteInstance) return false
        if (counterExample != other.counterExample) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + isEditable.hashCode()
        result = 31 * result + (counterExample?.hashCode() ?: 0)
        result = 31 * result + (concreteInstance?.hashCode() ?: 0)
        result = 31 * result + hybridRows.hashCode()
        result = 31 * result + selection.hashCode()
        result = 31 * result + columnHeaders.hashCode()
        result = 31 * result + rows.hashCode()
        result = 31 * result + freeVariableList.hashCode()
        result = 31 * result + durations.hashCode()
        result = 31 * result + name.hashCode()
        result = 31 * result + counterExample.hashCode()
        result = 31 * result + concreteInstance.hashCode()
        return result
    }


}
