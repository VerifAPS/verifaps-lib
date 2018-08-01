package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.SAssignment
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * Creates a modules that maintains the history of the given variables.
 * @author Alexander Weigl
 * @version 1 (31.07.18)
 */
open class HistoryModuleBuilder(
        val name: String = "History",
        val variables: List<SVariable>,
        val length: Int) : Runnable {

    val module = SMVModule(name)
    val moduleType = ModuleType(name, variables)

    init {
        assert(length > 0)
    }

    open fun addVariable(v: SVariable) {
        val first = SVariable("${v.name}_$0", v.dataType!!)
        module.moduleParameters.add(first)

        // state variables
        val vars = (1..length).map {
            SVariable("${v.name}_$$it", v.dataType!!)
        }
        module.stateVars.addAll(vars)

        val next = vars.toList()
        val from = vars.subList(0, vars.lastIndex).toMutableList()
        from.add(0, first)

        assert(next.size == from.size)

        next.zip(from).forEach { (n, f) ->
            module.nextAssignments.add(SAssignment(n, f))
        }
    }

    override fun run() {
        variables.forEach { addVariable(it) }
    }
}
