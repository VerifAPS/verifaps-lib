/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.DurationModifier
import edu.kit.iti.formal.automation.testtables.model.ProjectionVariable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.automation.testtables.model.options.Mode
import edu.kit.iti.formal.smv.HistoryModuleBuilder
import edu.kit.iti.formal.smv.ModuleType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.ast.SAssignment
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.smv.disjunction
import edu.kit.iti.formal.util.warn
import kotlin.math.abs

class SmvConstructionPipeline(state: AutomataTransformerState, superEnumType: SMVType) {

    val model = SMVConstructionModel(superEnumType, state)
    val transformers = arrayListOf<SmvConstructionTransformer>()

    init {
        model.testTable.ensureProgramRuns()

        transformers.add(GenerateSmvExpression)

        if (model.testTable.options.relational) {
            transformers.add(PlayPauseToAssumption)
            transformers.add(BackwardToAssumption)
        }

        transformers.add(RegisterDefines)
        transformers.add(DefineStateVariables)
        transformers.add(DefineProjectionVariables)
        transformers.add(InitialStates)
        transformers.add(DefineTransitions)
        transformers.add(NameSetterTransformer())
        transformers.add(ModuleParameterTransformer())
        transformers.add(ManagingGlobalVariables())
        transformers.add(BackwardsReferencesTransformer())

        when (state.testTable.options.mode) {
            Mode.CONFORMANCE -> {
                transformers.add(WeakConformance())
                transformers.add(LtlStrictConformance())
            }
            Mode.CONCRETE_TABLE -> transformers.add(ConcreteTableInvariantTransformer())
            Mode.INPUT_SEQUENCE_EXISTS -> transformers.add(InputSequenceInvariantTransformer())
            Mode.MONITOR_GENERATION -> TODO("not supported by this pipeline")
        }
    }

    fun transform(): SMVConstructionModel {
        transformers.forEach { a -> a.transform(model) }
        return model
    }
}

object DefineProjectionVariables : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.testTable.programVariables
            .filterIsInstance<ProjectionVariable>()
            .forEach {
                val zip = it.argumentDefinitions.zip(it.constraint)
                for ((v, expr) in zip) {
                    translate(model, v, expr)
                }
            }
    }

    private fun translate(model: SMVConstructionModel, variable: SVariable, expr: TestTableLanguageParser.ExprContext) {
        val smvExpr = GetetaFacade.exprToSmv(expr, model.testTable.parseContext)
        model.tableModule.definitions.add(SAssignment(variable, smvExpr))
    }
}

object DefineStateVariables : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.rowStates.map {
            model.getStateVariable(it)
        }.forEach {
            model.tableModule.stateVars.add(it)
        }
        model.tableModule.stateVars.add(model.stateError)
        model.tableModule.stateVars.add(model.stateSentinel)
    }
}

object InitialStates : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.rowStates.forEach {
            val v = model.getStateVariable(it)
            model.tableModule.initExpr.add(if (it in model.automaton.initialStates) v else v.not())
        }

        model.tableModule.initExpr.addAll(
            listOf(
                model.stateError.not(),
                model.stateSentinel.not(),
            ),
        )
    }
}

object DefineTransitions : AbstractTransformer<SMVConstructionModel>() {
    private lateinit var transitions: Map<AutomatonState, List<Transition>>
    override fun transform() {
        transitions = model.automaton.transitions.groupBy { it.to }
        model.rowStates.forEach {
            createNext(it)
        }
        createNext(model.automaton.stateError)
        createNext(model.automaton.stateSentinel)
    }

    private fun createNext(it: AutomatonState) {
        val expr =
            transitions[it]?.map { t ->
                when (t.type) {
                    TransitionType.ACCEPT -> model.getAccept(t.from as RowState)
                    TransitionType.ACCEPT_PROGRESS -> model.getAcceptProgress(t.from as RowState)
                    TransitionType.FAIL -> model.getFail(t.from as RowState)
                    TransitionType.TRUE -> model.getVariable(it)
                    TransitionType.MISS -> model.getMiss(t.from as RowState)
                }
            }?.disjunction() ?: SLiteral.FALSE
        model.tableModule.nextAssignments.add(SAssignment(model.getVariable(it), expr))
    }
}

object RegisterDefines : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.testTable.region.flat().forEach { rowDefinitions(model, it) }
        model.rowStates.forEach { stateDefines(model, it) }
    }

    fun rowDefinitions(model: SMVConstructionModel, s: TableRow) {
        // define input predicate
        model.define(s.defOutput, s.outputExpr)

        // define input predicate
        model.define(s.defInput, s.inputExpr)

        // progress indicator
        val progress = if (s.duration.pflag) {
            s.outgoing
                // TODO filter the sentinel out: .filter { it != model.sentinelState }
                .map { it.defInput }
                .disjunction()
        } else {
            SLiteral.FALSE
        }

        model.define(s.defProgress, s.defForward and progress.not())

        // define failed predicate
        model.define(s.defFailed, s.defInput and s.defOutput.not())

        // define forward predicate
        model.define(s.defForward, s.defInput and s.defOutput)
    }

    /**
     * defines the s_id_cnt_failed and s_id_cnt_fwd
     *
     * @param ss
     */
    private fun stateDefines(model: SMVConstructionModel, ss: RowState) {
        val stateVar = model.getStateVariable(ss)
        model.define(model.getAccept(ss), stateVar and ss.row.defForward)
        model.define(model.getFail(ss), stateVar and ss.row.defFailed)
        model.define(
            model.getAcceptProgress(ss),
            model.getAccept(ss) and ss.row.defProgress.not(),
        )
    }
}

internal val Duration.pflag: Boolean
    get() = this.modifier == DurationModifier.PFLAG_I || this.modifier == DurationModifier.PFLAG_IO

/**
 * Triggers the generation of the SMV expression with in the Rows.
 */
object GenerateSmvExpression : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.variableContext = model.testTable.parseContext
        model.testTable.generateSmvExpression()
    }
}

/**
 * Transfers the name of the table to the name of the SMV module.
 * Created by weigl on 17.12.16.
 */
class NameSetterTransformer : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        val mt = model.tableModule
        val gtt = model.testTable
        if (gtt.name.isEmpty()) {
            warn("No table name given. Using default name `table'.")
            gtt.name = "table"
        }
        mt.name = gtt.name
    }
}

/**
 * Every "pure" input variable (challenger) becomes a module parameter.
 *
 * Also maintains the [SMVConstructionModel.ttType]
 * Created by weigl on 17.12.16.
 */
class ModuleParameterTransformer : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.testTable.programVariables.forEach {
            model.tableModule.moduleParameters.add(it.internalVariable(model.variableContext.programRuns))
        }

        model.ttType = ModuleType(
            model.tableModule.name,
            model.testTable.programVariables.map {
                val a = it.externalVariable(
                    model.variableContext.programRuns,
                    "_${model.testTable.name}",
                )
                if (it.isAssertion) a.inNext() else a
            },
        )
    }
}

/**
 * Add global variables to the module.
 * Uses frozen variables and an invariant.
 * Created by weigl on 17.12.16.
 */
class ManagingGlobalVariables : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        val gtt = model.testTable
        val mt = model.tableModule
        for (cv in gtt.constraintVariables) {
            val svar = cv.internalVariable(gtt.programRuns)
            if (cv.dataType is EnumerateType) {
                svar.dataType = model.superEnumType
            }
            mt.frozenVars.add(svar)

            if (cv.constraint != null) {
                mt.initExpr.add(
                    GetetaFacade.exprToSMV(
                        cv.constraint!!,
                        svar,
                        0,
                        model.variableContext,
                    ),
                )
            }
            //            mt.invariants.add(svar equal svar.inNext())
        }
    }
}

class BackwardsReferencesTransformer : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        model.variableContext.refs.forEach { variable, history ->
            this.addDelayModule(model, variable, abs(history))
        }
    }

    private fun addDelayModule(model: SMVConstructionModel, variable: SVariable, history: Int) {
        val b = HistoryModuleBuilder("History_${history}_of_${variable.name}", listOf(variable), history)
        b.run()

        // Add Variable
        val svar = SVariable(GetetaFacade.getHistoryName(variable), b.moduleType)
        model.tableModule.stateVars.add(svar)

        // add helper module
        model.helperModules.add(b.module)
    }
}

/**
 * Created by weigl on 17.12.16.
 */
class WeakConformance : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        val invar =
            model.stateError implies
                model.rowStates.map { s -> model.getVariable(s) }
                    .disjunction(SLiteral.FALSE)
                    .or(model.stateSentinel)
        model.tableModule.invariantSpecs.add(invar)
    }
}

/**
 * Construction of the LTL specification for strict conformance.
 *
 * FAIRNESS -> F ( last_states_fwd | non_selected )
 *
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
class LtlStrictConformance : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        /*
        val steps = tt.testTable.region!!.flat()
        val lastStep = steps[steps.size - 1]
        val lastAutomataStep = lastStep.automataStates[lastStep.automataStates.size - 1]

        val lastStateForward = lastAutomataStep.defForward

        val automataStates = ArrayList<SMVExpr>(steps
                .flatMap { s -> s.automataStates }
                .map { `as` -> `as`.smvVariable.not() })
        automataStates.add(tt.errorVariable.not())

        val noStateSelected = SMVFacade
                .combine(SBinaryOperator.AND, automataStates)

        val fairness = steps
                .filter { state -> state.duration.isUnbounded }
                .flatMap { state -> state.outgoing }
                .filter { state -> state != tt.sentinelState }
                .map { it.defInput }
                .map { s -> s.eventually().globally() as SMVExpr }
                .reduce(SLiteral.TRUE) { a, b -> a.and(b) }

        val ltlspec = fairness
                .implies(noStateSelected.or(lastStateForward).eventually())

        tt.tableModule.ltlSpec.add(ltlspec)
         */
    }
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (17.12.16)
 */
class InputSequenceInvariantTransformer : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        /*
            exists an input and state pair in every turn
         */
        // TODO
        /*
        // one of the rows is always active
        val states = tt.testTable.region!!.flat()
                .flatMap { s -> s.automataStates }
                .map { v -> v.smvVariable as SMVExpr }
                .reduce { a, b -> a.or(b) }

        tt.tableModule.invariantSpecs.add(states)
         */
    }
}

/**
 * This transformer modifies the state in two ways
 *
 *  1. forbids the endSentinel state
 *  1. Strengthen forward definitions to the given cycles in the options
 *
 *
 * @author Alexander Weigl
 * @version 1 (24.12.16)
 */
class ConcreteTableInvariantTransformer : SmvConstructionTransformer {
    override fun transform(model: SMVConstructionModel) {
        val tableModule = model.tableModule
        tableModule.invariantSpecs.add(model.stateSentinel.not())
    }
}

private operator fun Iterable<SAssignment>.get(svar: SVariable): SAssignment? = find { it.target == svar }