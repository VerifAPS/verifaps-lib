package edu.kit.iti.formal.stvs.view.spec.variables.clipboard

import edu.kit.iti.formal.stvs.model.common.FreeVariable

/**
 * This class handles the conversion from a list of [FreeVariable] to JSON and vice versa.
 *
 * @author Philipp
 */
object Json {
    var json = Json

    /**
     * Generates JSON from variables.
     * @param freeVariables variables to convert
     * @return Stringified JSON version of variables
     */
    fun stringFromRealFreeVariables(freeVariables: List<FreeVariable>): String {
        return ""//return json.encodeToString(fromRealFreeVariables(freeVariables))
    }

    /**
     * Generates variables from JSON.
     * @param input Stringified JSON version of variables
     * @return restored variables
     */
    fun stringToRealFreeVariables(input: String?): List<FreeVariable> {
        //if (input == null)
        return listOf()
        //return toRealFreeVariables(json.decodeFromString<FreeVarSelection>(input))
    }

    /**
     * Generates a stringifyable [FreeVarSelection] from a list of [FreeVariable].
     * @param freeVariables variables to convert
     * @return converted selection
     */
    fun fromRealFreeVariables(freeVariables: List<FreeVariable>): FreeVarSelection {
        val vars = freeVariables.map { FreeVar(it.name, it.type, it.constraint) }
        return FreeVarSelection(vars)
    }

    /**
     * Generates a list of [FreeVariable] from the stringifyable class [FreeVarSelection].
     *
     * @param selection stringifyable selection
     * @return list of variables
     */
    fun toRealFreeVariables(selection: FreeVarSelection): List<FreeVariable> {
        return selection.selected.map { FreeVariable(it.name, it.type, it.defaultval) }
    }

    data class FreeVarSelection(var selected: List<FreeVar> = listOf())

    data class FreeVar(var name: String? = null, var type: String? = null, var defaultval: String? = null)
}
