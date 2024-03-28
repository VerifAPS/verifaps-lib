package edu.kit.iti.formal.stvs.model.common

import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue

/**
 * A list of free variables.
 * @author Philipp
 */
class FreeVariableList {
    private val variablesProperty = SimpleListProperty<FreeVariable>(FXCollections.observableArrayList())
    /**
     * Get the [ObservableList] of free variables. This list is "deeply observable", meaning
     * that changes to the properties of the [FreeVariable]s it contains cause change events
     * on the list.
     * @return The [ObservableList] of [FreeVariable]s
     */
    var variables: ObservableList<FreeVariable> by variablesProperty

    /**
     * Construct a FreeVariableList from a list of [FreeVariable]s.
     * @param variables The list of free variables
     */
    @JvmOverloads
    constructor(variables: MutableList<FreeVariable> = arrayListOf()) {
        this.variables = FXCollections.observableList(variables, FreeVariable.EXTRACTOR)
    }

    /**
     * Copy constructor for deep copies of a [FreeVariableList].
     *
     * @param freeVariableList the list to copy
     */
    constructor(freeVariableList: FreeVariableList) {
        val clonedVariables = arrayListOf<FreeVariable>()
        for (freeVar in freeVariableList.variables) {
            clonedVariables.add(FreeVariable(freeVar))
        }
        this.variables = FXCollections.observableList(clonedVariables, FreeVariable.EXTRACTOR)
    }
}
