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


import edu.kit.iti.formal.automation.testtables.exception.IllegalClockCyclesException
import edu.kit.iti.formal.automation.testtables.io.Report
import edu.kit.iti.formal.smv.ast.SAssignment
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * This transformer modifies the state in two ways
 *
 *  1. Adds a new state as the sentinel of the table
 *  1. forbids the sentinel state
 *  1. Strengthen forward definitions to the given cycles in the options
 *
 *
 * @author Alexander Weigl
 * @version 1 (24.12.16)
 */
class ConcreteTableInvariantTransformer : TableTransformer {
    override fun accept(tt: ConstructionModel) {
        val cto = tt.testTable.options.concreteTableOptions
        val rows = tt.testTable.region!!.flat()
        val tableModule = tt.tableModule

        val lastRow = rows[rows.size - 1].defForward
        val sentinel = SVariable.create("SENTINEL").asBool()

        // add state var
        tableModule.stateVars.add(sentinel)

        //add connection between last and sentinel
        tableModule.nextAssignments.add(
                SAssignment(sentinel, lastRow))
        tableModule.initAssignments.add(
                SAssignment(sentinel, SLiteral.FALSE))
        //forbid sentinel
        tableModule.invariantSpecs.add(sentinel.not())

        //Strengthen the _fwd literals
        rows.forEach outer@{ s ->
            val clock = tt.clocks[s]
            val id = s.id

            val cycles = cto.getCount(id, s.duration.lower)

            if (clock == null) {
                Report.info("Step %d has no clock, could not " + "enforce count of %d cycles.", id, cycles)
                return@outer
            }


            //validity check of user-wanted cycles
            if (!s.duration.contains(cycles)) {
                throw IllegalClockCyclesException(
                        String.format("Cycles %d are out of range [%d,%d] for State %d",
                                cycles, s.duration.lower, s.duration.upper, id))
            }

            // 0dX_<cycles>
            val count = SLiteral.create(cycles).with(clock!!.dataType!!)

            val fwd = tableModule.definitions[s.defForward]
            if(fwd!=null) {
                fwd.expr = fwd.expr.and(clock.equal(count))
            }
        }
    }
}

private operator fun Iterable<SAssignment>.get(svar: SVariable): SAssignment? {
    return find { it.target == svar }
}
