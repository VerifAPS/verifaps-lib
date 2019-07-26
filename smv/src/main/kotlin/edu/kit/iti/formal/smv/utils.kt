package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.*

/**Extensions**/

fun Iterable<SMVExpr>.joinToExpr(operator: SBinaryOperator): SMVExpr =
        this.reduce { a, b -> a.op(operator, b) }

fun Iterable<SMVExpr>.disjunction(): SMVExpr = this.joinToExpr(SBinaryOperator.OR)
fun Iterable<SMVExpr>.conjunction(): SMVExpr = this.joinToExpr(SBinaryOperator.AND)

fun Collection<SMVExpr>.joinToExpr(operator: SBinaryOperator = SBinaryOperator.AND, default: SMVExpr? = null): SMVExpr =
        if (size > 0 || default == null) {
            this.reduce { a, b -> a.op(operator, b) }
        } else {
            default

        }

fun Collection<SMVExpr>.disjunction(default: SMVExpr): SMVExpr =
        this.joinToExpr(SBinaryOperator.OR, default)

fun Collection<SMVExpr>.conjunction(default: SMVExpr): SMVExpr =
        this.joinToExpr(SBinaryOperator.AND, default)


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
