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

import edu.kit.iti.formal.automation.testtables.model.State
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.stream.Collectors

/**
 * Construction of the LTL specification for strict conformance.
 *
 *
 * FAIRNESS -> F ( last_states_fwd | non_selected )
 *
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
class LTLSpecTransformer : TableTransformer {
    override fun accept(tt: TableTransformation) {
        val steps = tt.testTable.region!!.flat()
        val lastStep = steps[steps.size - 1]
        val lastAutomataStep = lastStep.automataStates[lastStep.automataStates.size - 1]

        val lastStateForward = lastAutomataStep.defForward

        val automataStates = steps.stream()
                .flatMap<AutomatonState> { s -> s.automataStates.stream() }
                .map<SUnaryExpression> { `as` -> `as`.smvVariable.not() }
                .collect<List<SMVExpr>, Any>(Collectors.toList())
        automataStates.add(tt.errorState.not())

        val noStateSelected = SMVFacade
                .combine(SBinaryOperator.AND, automataStates)

        val fairness = steps.stream()
                .filter { state -> state.duration.isUnbounded }
                .flatMap { state -> state.outgoing.stream() }
                .filter { state -> state.id !== State.SENTINEL_ID }
                .map<SVariable>(Function<State, SVariable> { it.getDefInput() })
                .map { s -> s.eventually().globally() as SMVExpr }
                .reduce(SMVFacade.reducer(SBinaryOperator.AND))
                .orElse(SLiteral.TRUE)

        val ltlspec = fairness
                .implies(noStateSelected.or(lastStateForward).eventually())

        tt.tableModule.ltlSpec.add(ltlspec)
    }
}
