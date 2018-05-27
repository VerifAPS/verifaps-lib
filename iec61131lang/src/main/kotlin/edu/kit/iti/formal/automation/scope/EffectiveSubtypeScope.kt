package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.ast.MethodDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.st.util.Tuple

import java.util.*

class EffectiveSubtypeScope : HashMap<Tuple<String, String>, Set<AnyDt>>() {
    fun registerVariable(variable: VariableDeclaration) {
        if (!containsKey(tuple(variable, variable.parent!!)))
            put(tuple(variable, variable.parent!!), HashSet())
    }

    fun registerType(variable: VariableDeclaration, dataType: AnyDt) {
        get(tuple(variable, variable.parent!!)).add(dataType)
    }

    fun registerTypes(variable: VariableDeclaration, dataTypes: Collection<AnyDt>) {
        dataTypes.forEach { dt -> registerType(variable, dt) }
    }

    fun getTypes(variable: VariableDeclaration): Set<AnyDt> {
        return get(tuple(variable, variable.parent!!))
                ?: throw NoSuchElementException(tuple(variable, variable.parent!!).toString())
    }

    private fun tuple(variable: Identifiable, parent: Identifiable): Tuple<String, String> {
        return Tuple<S, T>(variable.name,
                if (parent is MethodDeclaration)
                    parent.parent!!.getIdentifier()
                else
                    parent.name)
    }
}
