/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.State
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import java.util.stream.Stream

/**
 * Creates the states and definition for each row and time including error and sentinel.
 * Created by weigl on 17.12.16.
 *
 * @version 3
 */
class StatesTransformer : AbstractTransformer() {
    override fun transform() {
        val flat = model.testTable.region.flat()
        flat.forEach { this.introduceState(it) }
        insertErrorState()
        insertSentinel()
    }

    private fun introduceState(s: State) {
        // define output predicate
        define(s.defOutput, SMVFacade
                .combine(SBinaryOperator.AND, s.outputExpr,
                        SLiteral.TRUE))

        // define input predicate
        define(s.defInput, SMVFacade
                .combine(SBinaryOperator.AND,
                        s.inputExpr, SLiteral.TRUE))

        // define failed predicate
        define(s.defFailed, SMVFacade
                .combine(SBinaryOperator.AND, s.defInput,
                        s.defOutput.not()))

        // define forward predicate
        define(s.defForward,
                SMVFacade.combine(SBinaryOperator.AND, s.defInput,
                        s.defOutput))

        if (s.duration.isDeterministicWait) {
            val collect = s.outgoing
                    .filter { k -> k != model.sentinelState }
                    .map { it.defInput }

            val outgoingIsValid =
                    SMVFacade.combine(SBinaryOperator.OR, collect, SLiteral.TRUE)

            define(s.defKeep,
                    SMVFacade.combine(SBinaryOperator.AND,
                            outgoingIsValid.not(), s.defInput, s.defOutput))
        }

        for (ss in s.automataStates) {
            introduceAutomatonStateDefines(ss)
            introduceAutomatonState(ss)
        }
    }

    /**
     * defines the s_id_cnt_failed and s_id_cnt_fwd
     *
     * @param ss
     */
    private fun introduceAutomatonStateDefines(ss: State.AutomatonState) {
        define(ss.defForward, SMVFacade
                .combine(SBinaryOperator.AND, ss.smvVariable,
                        ss.state.defForward))
        define(ss.defFailed, SMVFacade
                .combine(SBinaryOperator.AND, ss.smvVariable,
                        ss.state.defFailed))
    }

    /**
     * @param automatonState
     */
    private fun introduceAutomatonState(automatonState: State.AutomatonState) {
        val `var` = automatonState.smvVariable

        // sate variable
        model.tableModule.stateVars.add(`var`)

        //initialize state variable with true iff isStartState
        model.tableModule.initExpr.add(if (automatonState.isStartState) `var` else `var`.not())

        //If one predeccor is true, then we are true.
        var incoming: Stream<State.AutomatonState> = automatonState.incoming.stream()

        //remove self-loop on DET_WAIT, because we cannot use `_fwd`, we need `_keep`
        if (automatonState.state.duration.isDeterministicWait) {
            incoming = incoming.filter { `as` -> `as` != automatonState }
        }

        var activate = incoming
                .map { inc ->
                    var fwd: SMVExpr = inc.defForward
                    /* If incoming state is det.wait, then this state becomes only active
                     *  if it has not fired before.
                     */
                    if (inc.state.duration.isDeterministicWait) {
                        val inputAndState = automatonState.smvVariable.and(automatonState.state.defInput).not()
                        fwd = fwd.and(inputAndState)
                    }
                    fwd
                }
                .map { SMVExpr::class.java.cast(it) }
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE)


        if (automatonState.state.duration.isDeterministicWait) {
            // If this state is true, it stays true, until
            // no successor was correctly guessed.
            activate = activate.or(
                    `var`.and(automatonState.state.defKeep
                    ))
            //TODO add following state (s->!s_in)
        }

        /*
        if (automatonState.isUnbounded()) {
            or = SMVFacade.combine(SBinaryOperator.OR, or,
                    automatonState.getDefForward());
        }*/

        val assignment = SAssignment(
                automatonState.smvVariable, activate)
        model.tableModule.nextAssignments.add(assignment)
    }

    private fun insertErrorState() {
        // new error state
        model.tableModule.stateVars.add(model.errorVariable)

        // disable in the beginning
        model.tableModule.initExpr.add(model.errorVariable.not())

        val e = model.testTable.region.flat().stream()
                .flatMap { s -> s.automataStates.stream() }
                .map { s -> s.defFailed as SMVExpr }
                .reduce { a, b -> a.or(b) }
                .orElse(SLiteral.TRUE)
        val a = SAssignment(model.errorVariable, e)
        model.tableModule.nextAssignments.add(a)
    }

    private fun insertSentinel() {
        val sentinel = model.sentinelVariable
        val tm = model.tableModule
        tm.stateVars.add(sentinel)
        tm.initExpr.add(sentinel.not())
        val e = model.sentinelState.automataStates[0].incoming.stream()
                .map { it.defForward }
                .map { fwd -> fwd as SMVExpr }
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE)
        val a = SAssignment(sentinel, e.or(sentinel))
        tm.nextAssignments.add(a)
    }

    private fun define(defOutput: SVariable, combine: SMVExpr) {
        model.tableModule.definitions[defOutput] = combine
    }
}

private val Duration.isDeterministicWait: Boolean
    get() =
        when (this) {
            is Duration.OpenInterval -> pflag
            is Duration.ClosedInterval -> pflag
            else -> false
        }
