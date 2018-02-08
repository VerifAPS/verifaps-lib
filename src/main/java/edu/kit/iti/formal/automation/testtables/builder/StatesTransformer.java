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
package edu.kit.iti.formal.automation.testtables.builder;


import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.model.TableModule;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Creates the states and definition for each row and time including error and sentinel.
 * Created by weigl on 17.12.16.
 *
 * @version 3
 */
public class StatesTransformer implements TableTransformer {
    private TableModule mt;
    private GeneralizedTestTable gtt;
    private SVariable errorState;
    private SVariable sentinelState;
    private State sentinel;

    private void createStates() {
        List<State> flat = gtt.getRegion().flat();
        flat.forEach(this::introduceState);
        insertErrorState();
        insertSentinel();
    }

    private void introduceState(State s) {
        // define output predicate
        define(s.getDefOutput(), SMVFacade
                .combine(SBinaryOperator.AND, s.getOutputExpr(),
                        SLiteral.TRUE));

        // define input predicate
        define(s.getDefInput(), SMVFacade
                .combine(SBinaryOperator.AND,
                        s.getInputExpr(), SLiteral.TRUE));

        // define failed predicate
        define(s.getDefFailed(), SMVFacade
                .combine(SBinaryOperator.AND, s.getDefInput(),
                        s.getDefOutput().not()));

        // define forward predicate
        define(s.getDefForward(),
                SMVFacade.combine(SBinaryOperator.AND, s.getDefInput(),
                        s.getDefOutput()));

        if (s.getDuration().isDeterministicWait()) {
            List<SMVExpr> collect = s.getOutgoing().stream()
                    .filter(k -> !k.getId().equals(State.SENTINEL_ID))
                    .map(State::getDefInput)
                    .collect(Collectors.toList());
            SMVExpr outgoingIsValid =
                    collect.size() > 0
                            ? SMVFacade.combine(SBinaryOperator.OR, collect)
                            : SLiteral.TRUE;

            define(s.getDefKeep(),
                    SMVFacade.combine(SBinaryOperator.AND,
                            outgoingIsValid.not(), s.getDefInput(), s.getDefOutput()
                    ));
        }

        for (State.AutomatonState ss : s.getAutomataStates()) {
            introduceAutomatonStateDefines(ss);
            introduceAutomatonState(ss);
        }
    }

    /**
     * defines the s_id_cnt_failed and s_id_cnt_fwd
     *
     * @param ss
     */
    private void introduceAutomatonStateDefines(State.AutomatonState ss) {
        define(ss.getDefForward(), SMVFacade
                .combine(SBinaryOperator.AND, ss.getSMVVariable(),
                        ss.getState().getDefForward()));
        define(ss.getDefFailed(), SMVFacade
                .combine(SBinaryOperator.AND, ss.getSMVVariable(),
                        ss.getState().getDefFailed()));
    }

    /**
     * @param automatonState
     */
    private void introduceAutomatonState(State.AutomatonState automatonState) {
        SVariable var = automatonState.getSMVVariable();

        // sate variable
        mt.getStateVars().add(var);

        //initialize state variable with true iff isStartState
        mt.getInit().add(automatonState.isStartState() ? var : var.not());

        //If one predeccor is true, then we are true.
        Stream<State.AutomatonState> incoming = automatonState.getIncoming().stream();

        //remove self-loop on DET_WAIT, because we cannot use `_fwd`, we need `_keep`
        if (automatonState.getState().getDuration().isDeterministicWait()) {
            incoming = incoming.filter(as -> !as.equals(automatonState));
        }

        SMVExpr activate = incoming
                .map(State.AutomatonState::getDefForward)
                .map(fwd -> (SMVExpr) fwd)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE);

        if (automatonState.getState().getDuration().isDeterministicWait()) {
            // If this state is true, it stays true, until
            // no successor was correctly guessed.
            activate = activate.or(
                    var.and(automatonState.getState().getDefKeep()
                    ));
        }

        /*
        if (automatonState.isUnbounded()) {
            or = SMVFacade.combine(SBinaryOperator.OR, or,
                    automatonState.getDefForward());
        }*/

        SAssignment assignment = new SAssignment(
                automatonState.getSMVVariable(), activate);
        mt.getNextAssignments().add(assignment);
    }

    private void insertErrorState() {
        // new error state
        mt.getStateVars().add(errorState);

        // disable in the beginning
        mt.getInit().add(errorState.not());

        SMVExpr e = gtt.getRegion().flat().stream()
                .flatMap(s -> s.getAutomataStates().stream())
                .map(s -> (SMVExpr) s.getDefFailed())
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.TRUE);
        SAssignment a = new SAssignment(errorState, e);
        mt.getNextAssignments().add(a);
    }

    private void insertSentinel() {
        mt.getStateVars().add(sentinelState);
        mt.getInit().add(sentinelState.not());
        SMVExpr e = sentinel.getAutomataStates().get(0).getIncoming().stream()
                .map(State.AutomatonState::getDefForward)
                .map(fwd -> (SMVExpr) fwd)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE);
        SAssignment a = new SAssignment(sentinelState, e.or(sentinelState));
        mt.getNextAssignments().add(a);
    }

    private void define(SVariable defOutput, SMVExpr combine) {
        mt.getDefinitions().put(defOutput, combine);
    }

    @Override
    public void accept(TableTransformation tt) {
        mt = tt.getTableModule();
        gtt = tt.getTestTable();
        errorState = tt.getErrorState();
        sentinelState = tt.getSentinelState();
        sentinel = tt.getReachable().getSentinel();
        createStates();
    }
}
