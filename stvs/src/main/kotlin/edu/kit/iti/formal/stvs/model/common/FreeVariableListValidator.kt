package edu.kit.iti.formal.stvs.model.common

import edu.kit.iti.formal.stvs.model.expressions.*
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue
import java.util.*

/**
 * The validator for the effective model [FreeVariableList]. This class provides
 * automatically updating properties for the formal model
 * (see [.validFreeVariablesProperty]) and for any
 * problems encountered while validating (see [.problemsProperty]).
 *
 * @author Philipp
 */
class FreeVariableListValidator(
    private val typeContext: ListProperty<Type>,
    private val freeVariables: FreeVariableList
) {
    val problemsProperty = SimpleMapProperty<FreeVariable, MutableList<FreeVariableProblem>>(FXCollections.observableHashMap())
    var problems by problemsProperty

    val validFreeVariablesProperty = SimpleListProperty(FXCollections.observableArrayList<ValidFreeVariable>())
    val validFreeVariables: ObservableList<ValidFreeVariable> by validFreeVariablesProperty

    private val valid: BooleanProperty = SimpleBooleanProperty(false)

    /**
     * Creates a validator with the given formal type context model for the effective
     * free variable model.
     *
     * @param typeContext the context for validating the free variables and generating the valid
     * free variables
     * @param freeVariables the free variables model to validate
     */
    init {
        freeVariables.variables.addListener { _: Observable? -> revalidate() }
        typeContext.addListener { _: Observable? -> revalidate() }
        revalidate()
    }

    /**
     * Starts the validation algorithm and updates the [.validFreeVariablesProperty] and
     * the [.problemsProperty].
     */
    fun revalidate() {
        val typesByName = typeContext.get().associateBy { obj -> obj.typeName }
        val variableMap = freeVariables.variables
            .associate { it.name to (typesByName[it.type] ?: error("Type ${it.type} is unknown")) }

        val validated = arrayListOf<ValidFreeVariable>()

        freeVariables.variables.forEach { freeVariable: FreeVariable ->
            val problem = DuplicateFreeVariableProblem.checkForDuplicates(
                freeVariable, freeVariables.variables
            )
            if (problem == null) {
                try {
                    validated.add(
                        InvalidFreeVariableProblem.tryToConvertToValid(freeVariable, typesByName, variableMap)
                    )
                } catch (problem: InvalidFreeVariableProblem) {
                    problems.computeIfAbsent(freeVariable) { arrayListOf() }.add(problem)
                }
            } else {
                problems.computeIfAbsent(freeVariable) { arrayListOf() }.add(problem)
            }
        }

        validFreeVariablesProperty.setAll(validated)
        valid.set(problems.isEmpty())
    }

    fun validProperty(): ReadOnlyBooleanProperty {
        return valid
    }

}
