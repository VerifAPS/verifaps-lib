package edu.kit.iti.formal.automation.testtables;

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
import edu.kit.iti.formal.automation.testtables.model.Region;
import edu.kit.iti.formal.automation.testtables.model.State;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Calculation of the State/Row reachability.
 * <p>
 * A <i>i</i>th row can reach (directly) the <i>j</i>th row iff
 * </p>
 * <ol>
 * <li><i>(i+1)</i>th can reach the <i>j</i>th row and the duration
 * of <i>i+1</i> can be zero ({@link edu.kit.iti.formal.automation.testtables.model.Duration}.getLower() == 0).
 * </li>
 * <li>
 * <i>i</i>th row is the end of block and <i>j</i>th row is the beginning of the same block.
 * </li>
 * </ol>
 * <p>
 * This resolution is programmed as a fixpoint algorithm.
 * </p>
 * <p>
 * Currently supports of blocks and arbitrary durations.
 * </p>
 *
 * @author Alexander Weigl
 * @version 2 (12.12.16)
 */
public class StateReachability {
    private final GeneralizedTestTable gtt;
    private final List<State> flatList;

    public StateReachability(GeneralizedTestTable table) {
        gtt = table;
        flatList = gtt.getRegion().flat();

        initTable();
        addRegions(gtt.getRegion());
        fixpoint();
        maintainIncomning();
        maintainAutomata();
        isInitialReachable();
    }

    private void maintainAutomata() {
        for (State state : flatList) {
            List<State.AutomatonState> astates = state.getAutomataStates();
            for (int i = 0; i < astates.size(); i++) {
                final State.AutomatonState a = astates.get(i);

                if (a.isFirst()) {
                    State s = a.getState();
                    s.getIncoming().stream()
                            .flatMap(as -> as.getAutomataStates().stream())
                            .filter(State.AutomatonState::isOptional)
                            .forEach(b -> connect(b, a));
                }

                //
                if (i + 1 < astates.size()) {
                    connect(a, astates.get(i + 1));
                }

                //connect to first automata state in every next row
                if (a.isOptional()) {
                    state.getOutgoing().forEach(next -> {
                        connect(a, next.getAutomataStates().get(0));
                    });
                }

                if (a.isUnbounded()) {
                    connect(a, a);
                }
            }
        }
    }

    private void connect(State.AutomatonState a, State.AutomatonState b) {
        a.getOutgoing().add(b);
        b.getIncoming().add(a);
    }

    private void maintainIncomning() {
        for (State out : flatList) {
            for (State in : out.getOutgoing()) {
                in.getIncoming().add(out);
            }
        }
    }

    /**
     * The fixpoint algorithm.
     * Needs to be initialize with the direct reachable of i to i+1 and the region borders.
     */
    private void fixpoint() {
        boolean changed = true;
        while (changed) { // as long we have changes
            changed = false;
            //for each row
            for (State state : flatList) {
                int oldSize = state.getOutgoing().size();
                Set<State> reached = new HashSet<>(flatList.size());
                //foreach reachable state
                for (State reachable : state.getOutgoing()) {
                    // if reachable state is isSkippable, add their reachable state list
                    if (reachable.getDuration().isSkippable()) {
                        reached.addAll(reachable.getOutgoing());
                    }
                }
                //add to the outgoing
                state.getOutgoing().addAll(reached);
                //check for size
                changed = changed || state.getOutgoing().size() != oldSize;
            }

        }
    }

    /**
     * initialize the region borders
     *
     * @param r
     */
    private void addRegions(Region r) {
        if (r.getDuration().getUpper() > 1) {
            r.getStates().get(r.getStates().size() - 1).getOutgoing()
                    .add(r.getStates().get(0));
        }

        //Regions can be isSkippable
        r.getStates().stream().filter(s -> s instanceof Region).forEach(s -> {
            Region region = (Region) s;
            addRegions(region);
        });
    }

    /**
     * i-th row can reach (i+1)-th row
     */
    private void initTable() {
        for (int i = 0; i < flatList.size() - 1; i++) {
            flatList.get(i).getOutgoing().add(flatList.get(i + 1));
        }
    }

    private void isInitialReachable() {
        Queue<State> queue = new LinkedList<>();
        queue.add(flatList.get(0));
        while (!queue.isEmpty()) {
            State s = queue.remove();
            //already reached
            if (s.isInitialReachable())
                continue;

            s.setInitialReachable(true);

            if (s.getDuration().isSkippable())
                queue.addAll(s.getOutgoing());
        }
    }
}