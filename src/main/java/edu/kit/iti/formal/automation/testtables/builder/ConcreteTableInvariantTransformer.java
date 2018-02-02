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

import edu.kit.iti.formal.automation.testtables.exception.IllegalClockCyclesException;
import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.model.TableModule;
import edu.kit.iti.formal.automation.testtables.model.options.ConcreteTableOptions;
import edu.kit.iti.formal.smv.ast.SAssignment;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.List;

/**
 * This transformer modifies the state in two ways
 * <ol>
 * <li>Adds a new state as the sentinel of the table</li>
 * <li>forbids the sentinel state</li>
 * <li>Strengthen forward definitions to the given cycles in the options</li>
 * </ol>
 *
 * @author Alexander Weigl
 * @version 1 (24.12.16)
 */
public class ConcreteTableInvariantTransformer implements TableTransformer {
    @Override
    public void accept(TableTransformation tt) {
        final ConcreteTableOptions cto = tt.getTestTable().getOptions().getConcreteTableOptions();
        final List<State> rows = tt.getTestTable().getRegion().flat();
        final TableModule tableModule = tt.getTableModule();

        SVariable lastRow = rows.get(rows.size() - 1).getDefForward();
        SVariable sentinel = SVariable.create("SENTINEL").asBool();

        // add state var
        tableModule.getStateVars().add(sentinel);

        //add connection between last and sentinel
        tableModule.getNextAssignments().add(
                new SAssignment(sentinel, lastRow));
        tableModule.getInitAssignments().add(
                new SAssignment(sentinel, SLiteral.FALSE));
        //forbid sentinel
        tableModule.getInvarSpec().add(sentinel.not());

        //Strengthen the _fwd literals
        rows.forEach(s -> {
            SMVExpr clock = tableModule.getClocks().get(s);
            int id = s.getId();

            int cycles = cto.getCount(id, s.getDuration().getLower());

            if (clock == null) {
                Report.info("Step %d has no clock, could not " +
                        "enforce count of %d cycles.", id, cycles);
                return;
            }


            //validity check of user-wanted cycles
            if (!s.getDuration().contains(cycles)) {
                throw new IllegalClockCyclesException(
                        String.format("Cycles %d are out of range [%d,%d] for State %d",
                                cycles, s.getDuration().getLower(), s.getDuration().getUpper(), id));
            }

            // 0dX_<cycles>
            SMVExpr count = SLiteral.create(cycles)
                    .as(clock.getSMVType());

            SMVExpr fwd = tableModule.getDefinitions().get(s.getDefForward());
            tableModule.getDefinitions().put(s.getDefForward(),
                    fwd.and(clock.equal(count)));
        });
    }
}
