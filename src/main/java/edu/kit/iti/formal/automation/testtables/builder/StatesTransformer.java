package edu.kit.iti.formal.automation.testtables.builder;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.model.TableModule;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

import java.util.List;

/**
 * Created by weigl on 17.12.16.
 *
 * @version 2
 */
public class StatesTransformer implements TableTransformer {
    private TableModule mt;
    private GeneralizedTestTable gtt;
    private SVariable errorState;

    private void createStates() {
        List<State> flat = gtt.getRegion().flat();
        flat.forEach(this::introduceState);
        insertErrorState();
    }

    private void introduceState(State s) {
        // define output predicate
        define(s.getDefOutput(), SMVFacade
                .combine(SBinaryOperator.AND, s.getOutputExpr(),
                        SLiteral.TRUE));

        // define input predicate
        define(s.getDefInput(), SMVFacade
                .combine(SBinaryOperator.AND, s.getInputExpr(), SLiteral.TRUE));

        // define failed predicate
        define(s.getDefFailed(), SMVFacade
                .combine(SBinaryOperator.AND, s.getDefInput(),
                        s.getDefOutput().not()));

        // define forward predicate
        define(s.getDefForward(), SMVFacade
                .combine(SBinaryOperator.AND, s.getDefInput(),
                        s.getDefOutput()));

        for (State.AutomatonState ss : s.getAutomataStates()) {
            introduceAutomatonStateDefinitions(ss);
            introduceAutomatonState(ss);
        }

    }

    /**
     * defines the s_id_cnt_failed and s_id_cnt_fwd
     *
     * @param ss
     */
    private void introduceAutomatonStateDefinitions(State.AutomatonState ss) {
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
        mt.getStateVars().add(var);
        mt.getInit().add(automatonState.isStartState() ? var : var.not());

        SMVExpr or = automatonState.getIncoming().stream()
                .map(State.AutomatonState::getDefForward)
                .map(fwd -> (SMVExpr) fwd)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElse(SLiteral.FALSE);

        if (automatonState.isUnbounded()) {
            or = SMVFacade.combine(SBinaryOperator.OR, or,
                    automatonState.getDefFailed());
        }

        SAssignment assignment = new SAssignment(
                automatonState.getSMVVariable(), or);
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

    private void define(SVariable defOutput, SMVExpr combine) {
        mt.getDefinitions().put(defOutput, combine);
    }

    @Override public void accept(TableTransformation tt) {
        mt = tt.getTableModule();
        gtt = tt.getTestTable();
        errorState = tt.getErrorState();
        createStates();
    }
}
