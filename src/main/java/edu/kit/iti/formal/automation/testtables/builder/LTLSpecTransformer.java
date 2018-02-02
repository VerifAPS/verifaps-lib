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

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.SBinaryOperator;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Construction of the LTL specification for strict conformance.
 * <p>
 * FAIRNESS -> F ( last_states_fwd | non_selected )
 *
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
public class LTLSpecTransformer implements TableTransformer {
    @Override
    public void accept(TableTransformation tt) {
        List<State> steps = tt.getTestTable().getRegion().flat();
        State lastStep = steps.get(steps.size() - 1);
        State.AutomatonState lastAutomataStep = lastStep.getAutomataStates()
                .get(lastStep.getAutomataStates().size() - 1);

        SVariable lastStateForward = lastAutomataStep.getDefForward();

        List<SMVExpr> automataStates = steps.stream()
                .flatMap(s -> s.getAutomataStates().stream())
                .map(as -> as.getSMVVariable().not())
                .collect(Collectors.toList());
        automataStates.add(tt.getErrorState().not());

        SMVExpr noStateSelected = SMVFacade
                .combine(SBinaryOperator.AND, automataStates);

        SMVExpr fairness = steps.stream()
                .filter(state -> state.getDuration().isUnbounded())
                .flatMap(state -> state.getOutgoing().stream())
                .filter(state -> state.getId() != -1)
                .map(State::getDefInput)
                .map(s -> (SMVExpr) s.eventually().globally())
                .reduce(SMVFacade.reducer(SBinaryOperator.AND))
                .orElse(SLiteral.TRUE);

        SMVExpr ltlspec = fairness
                .implies(noStateSelected.or(lastStateForward).eventually());

        tt.getTableModule().getLTLSpec().add(ltlspec);
    }
}
