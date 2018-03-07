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

import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SMVExpr

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
    override fun accept(tt: ConstructionModel) {
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
                .reduce { a, b -> a.and(b) }

        val ltlspec = fairness
                .implies(noStateSelected.or(lastStateForward).eventually())

        tt.tableModule.ltlSpec.add(ltlspec)
    }
}
