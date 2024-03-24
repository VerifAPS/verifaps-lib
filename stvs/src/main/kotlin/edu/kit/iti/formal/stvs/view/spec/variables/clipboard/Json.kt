package edu.kit.iti.formal.stvs.view.spec.variables.clipboard

import com.google.gson.Gson
import edu.kit.iti.formal.stvs.model.common.FreeVariable
import java.util.stream.Collectors

/**
 * This class handles the conversion from a list of [FreeVariable] to JSON and vice versa.
 *
 * @author Philipp
 */
object Json {
    private val GSON = Gson()

    /**
     * Generates JSON from variables.
     * @param freeVariables variables to convert
     * @return Stringified JSON version of variables
     */
    fun stringFromRealFreeVariables(freeVariables: List<FreeVariable>): String {
        return GSON.toJson(fromRealFreeVariables(freeVariables), FreeVarSelection::class.java)
    }

    /**
     * Generates variables from JSON.
     * @param input Stringified JSON version of variables
     * @return restored variables
     */
    fun stringToRealFreeVariables(input: String?): List<FreeVariable> {
        return toRealFreeVariables(GSON.fromJson(input, FreeVarSelection::class.java))
    }

    /**
     * Generates a stringifyable [FreeVarSelection] from a list of [FreeVariable].
     * @param freeVariables variables to convert
     * @return converted selection
     */
    fun fromRealFreeVariables(freeVariables: List<FreeVariable>): FreeVarSelection {
        val vars = freeVariables.stream().map { freeVariable: FreeVariable ->
            val `var` = FreeVar()
            `var`.name = freeVariable.name
            `var`.type = freeVariable.type
            `var`.defaultval = freeVariable.constraint
            `var`
        }.collect(Collectors.toList())
        val selection = FreeVarSelection()
        selection.selected = vars
        return selection
    }

    /**
     * Generates a list of [FreeVariable] from the stringifyable class [FreeVarSelection].
     *
     * @param selection stringifyable selection
     * @return list of variables
     */
    fun toRealFreeVariables(selection: FreeVarSelection): List<FreeVariable> {
        return selection.selected!!.stream()
            .map { freeVar: FreeVar -> FreeVariable(freeVar.name, freeVar.type, freeVar.defaultval) }
            .collect(Collectors.toList())
    }

    class FreeVarSelection {
        var selected: List<FreeVar>? = null
    }

    class FreeVar {
        var name: String? = null
        var type: String? = null
        var defaultval: String? = null
    }
}
