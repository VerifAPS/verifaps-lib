package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.common.*
import javafx.beans.Observable
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
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
    private val counterExample = NullableProperty<ConcreteSpecification?>()
    private val concreteInstance = NullableProperty<ConcreteSpecification?>()
    val hybridRows: ObservableList<HybridRow> = FXCollections.observableArrayList()

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
    ) : this(SpecificationTable.Companion.DEFAULT_NAME, freeVariableList, editable)

    /**
     * Create a new, empty hybrid specification with a given name and a list of free variables.
     *
     * @param name The name of the HybridSpecification
     * @param freeVariableList A list of initial free variables
     * @param editable True if this HybridSpecification is editable, false otherwise
     */
    init {
        hybridRows.addListener(ListChangeListener<HybridRow> { change ->
            this.onHybridRowChanged(change)
        })
        counterExample.addListener { event: Observable? -> onCounterExampleChanged() }
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
            row.updateCounterExampleCells(rowIndex, getCounterExample())
            hybridRows.add(row)
        }
    }

    private fun onCounterExampleChanged() {
        for (rowIndex in rows.indices) {
            hybridRows[rowIndex]!!.updateCounterExampleCells(rowIndex, getCounterExample())
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

    fun getCounterExample() = counterExample.get()

    /**
     * Sets the counterexample for this hybrid specification. This will automatically update
     * the [HybridRow]'s counterexample cells in [.getHybridRows] from the given
     * counterexample.
     *
     * @param counterExample the concrete specification to be shown in-place in the gui
     * @throws IllegalArgumentException if the given concrete instance's column headers don't match
     * this specification's column headers
     */
    fun setCounterExample(counterExample: ConcreteSpecification?) {
        if (counterExample != null) {
            require(columnHeadersMatch(counterExample.columnHeaders)) {
                ("The column headers of the concrete instance are not "
                        + "compatible with this hybrid specification")
            }
            this.counterExample.set(counterExample)
        }
    }

    fun getSelection(): Selection = selection

    fun getConcreteInstance(): ConcreteSpecification? = concreteInstance.get()

    fun concreteInstanceProperty(): NullableProperty<ConcreteSpecification?> = concreteInstance

    fun counterExampleProperty(): NullableProperty<ConcreteSpecification?> = counterExample

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
    fun setConcreteInstance(concreteInstance: ConcreteSpecification?) {
        if (concreteInstance != null) {
            require(columnHeadersMatch(concreteInstance.columnHeaders)) {
                ("The column headers of the concrete instance are not "
                        + "compatible with this hybrid specification")
            }
            this.concreteInstance.set(concreteInstance)
        }
    }

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
        concreteInstance.set(null)
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (getCounterExample() != null) getCounterExample().hashCode() else 0)
        result = 31 * result + (if (getConcreteInstance() != null) getConcreteInstance().hashCode() else 0)
        result = 31 * result + (if (isEditable) 1 else 0)
        result = 31 * result + (if (hybridRows != null) hybridRows.hashCode() else 0)
        result = 31 * result + (if (getSelection() != null) getSelection().hashCode() else 0)
        return result
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }
        if (!super.equals(obj)) {
            return false
        }

        val that = obj as HybridSpecification

        if (isEditable != that.isEditable) {
            return false
        }
        if (if (getCounterExample() != null) getCounterExample() != that.getCounterExample()
            else that.getCounterExample() != null
        ) {
            return false
        }
        if (if (getConcreteInstance() != null) getConcreteInstance() != that.getConcreteInstance()
            else that.getConcreteInstance() != null
        ) {
            return false
        }
        if (if (hybridRows != null) hybridRows != that.hybridRows
            else that.hybridRows != null
        ) {
            return false
        }
        return if (getSelection() != null) getSelection() == that.getSelection() else that.getSelection() == null
    }
}
