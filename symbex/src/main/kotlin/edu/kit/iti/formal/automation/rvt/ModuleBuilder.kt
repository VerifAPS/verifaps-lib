package edu.kit.iti.formal.automation.rvt

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.rvt.translators.DefaultValueTranslator
import edu.kit.iti.formal.automation.rvt.translators.TypeTranslator
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.ast.SAssignment
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.meta
import java.util.*
import kotlin.collections.HashMap

public val SVariable.info: SmvVariableInfo
    get() {
        return meta<SmvVariableInfo>() ?: SmvVariableInfo().also { meta<SmvVariableInfo>(it) }
    }

public var SVariable.isInput: Boolean
    get() = info.isInput
    set(value) {
        info.isInput = value
    }

public var SVariable.isOutput: Boolean
    get() = info.isOutput
    set(value) {
        info.isOutput = value
    }

data class SmvVariableInfo(var isInput: Boolean = false, var isOutput: Boolean = false)

class DefinitionReducer(private val module: SMVModule) {
    private val definitionsForSurvival = ArrayList<SAssignment>(module.definitions.size)
    private val substitutions = HashMap<SVariable, SVariable>()
    fun identifiedTrivialDefinitions(): Unit {
        module.definitions.forEach { assign ->
            val (k, v) = assign
            if (v is SVariable) {
                substitutions[k] = v
            } else {
                definitionsForSurvival.add(assign)
            }
        }
    }

    fun findFixpoints() {
        var change: Boolean
        do {
            change = false
            val newSubs = HashMap<SVariable, SVariable>(substitutions.size)
            for ((from, to) in substitutions) {
                if (to in substitutions) {
                    newSubs[from] = substitutions[to]!!
                    change = true
                } else {
                    newSubs[from] = to
                }
            }
            substitutions.clear()
            substitutions.putAll(newSubs)
        } while (change)
    }

    fun substitute() {
        identifiedTrivialDefinitions()
        findFixpoints()
        module.accept(ExpressionReplacer(substitutions))
        module.definitions.clear()
        module.definitions.addAll(definitionsForSurvival)
    }
}

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
class ModuleBuilder(val program: PouExecutable,
                    finalState: SymbolicState,
                    val reduceDefinitions: Boolean = true) : Runnable {
    val state = finalState//.unfolded()


    val module = SMVModule(program.name)
    //val vardeps: VariableDependency = VariableDependency(finalState)
    //private Map<VariableDeclaration, SVariable> vars = new HashMap<>();

    var typeTranslator: TypeTranslator = DefaultTypeTranslator.INSTANCE
    var valueTranslator = DefaultValueTranslator.INSTANCE
    var initValueTranslator: InitValueTranslator = DefaultInitValue

    override fun run() {
        module.name = program.name

        val outputVars = HashSet(program.scope
                .filterByFlags(VariableDeclaration.OUTPUT))

        val inputVars = program.scope
                .filterByFlags(VariableDeclaration.INPUT)

        // TODO fix so this terminates
        //Set<SVariable> stateVariables = vardeps.dependsOn(outputVars, inputVars);

        // Using this workaround instead
        val stateVariables = state.keys
                .filter { (name) ->
                    inputVars.stream().noneMatch { v2 -> v2.name == name }
                }

        val outputVarNames = outputVars.map(VariableDeclaration::name)
        for (`var` in stateVariables) {
            if (outputVarNames.contains(`var`.name)) {
                `var`.isOutput = true
            }
        }

        insertDefinitions(state.getAllDefinitions())
        insertVariables(stateVariables)
        insertInputVariables(inputVars)

        if (reduceDefinitions) {
            val dr = DefinitionReducer(module)
            dr.substitute()
        }
    }

    private fun insertDefinitions(definitions: Map<SVariable, SMVExpr>) {
        definitions.forEach { (k, v) -> addDefinition(k, v) }
    }

    private fun addDefinition(k: SVariable, v: SMVExpr) =
            module.definitions.add(SAssignment(k, v))

    private fun insertInputVariables(decls: List<VariableDeclaration>) {
        decls.map { this.typeTranslator.translate(it) }
                .forEach { v ->
                    v.isInput = true
                    module.moduleParameters.add(v)
                }
    }

    private fun insertVariables(variables: Collection<SVariable>) {
        for (v in variables) {
            addVarDeclaration(v)
            addInitAssignment(v)
            addNextAssignment(v)
        }
    }

    private fun addVarDeclaration(s: SVariable) {
        module.stateVars.add(s)
    }

    private fun addInitAssignment(variable: SVariable) {
        val s = program.scope.getVariable(variable.name)
        val e: SMVExpr
        if (s!!.init != null) {
            val sv = s.init as Literal?
            e = sv!!.accept(SymbolicExecutioner())!!
        } else {
            e = this.valueTranslator.translate(
                    this.initValueTranslator.getInit(s.dataType!!))
        }
        val a = SAssignment(variable, e)
        module.initAssignments.add(a)
    }

    private fun addNextAssignment(s: SVariable) {
        val e = state[s]
        val a = SAssignment(s, e!!)
        module.nextAssignments.add(a)
    }
}
