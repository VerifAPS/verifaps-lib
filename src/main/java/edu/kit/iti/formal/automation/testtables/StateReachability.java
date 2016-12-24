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

import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.Region;
import edu.kit.iti.formal.automation.testtables.model.State;

import java.util.*;
import java.util.stream.Stream;

/**
 * Calculation of the State/Row reachability.
 * <p>
 * <p>
 * A <i>i</i>th row can reach (directly) the <i>j</i>th row iff
 * <ol>
 * <li><i>(i+1)</i>th can reach the <i>j</i>th row and the duration
 * of <i>i+1</i> can be zero ({@link edu.kit.iti.formal.automation.testtables.model.Duration}.getLower() == 0).
 * </li>
 * <li>
 * <i>i</i>th row is the end of block and <i>j</i>th row is the beginning of the same block.
 * </li>
 * </ol>
 * </p>
 * <p>
 * This resolution is programmed as a fixpoint algorithm.
 * <p>
 * Currently supports of blocks and arbitrary durations.
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class StateReachability {
    private final GeneralizedTestTable gtt;
    private final Map<State, Set<State>> reachability = new HashMap<>();
    private final List<State> flatList;

    public StateReachability(GeneralizedTestTable table) {
        gtt = table;
        flatList = gtt.getRegion().flat();
        initTable();
        addRegions(gtt.getRegion());
        fixpoint();

        // report
        reachability.forEach((k, v) -> {
            Report.debug("Row %d can reach: {%s}",
                    k.getId(),
                    v.stream()
                            .map(State::getId)
                            .map(Object::toString)
                            .reduce((a, b) -> a + ", " + b).orElse(""));
        });
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
            for (Map.Entry<State, Set<State>> current : reachability.entrySet()) {
                //copy because of failsafe
                Set<State> reachables = new HashSet<>(current.getValue());
                //foreach reachable state
                for (State reachable : reachables) {
                    // if reachable state is skippable, add their reachable state list
                    if (reachable.getDuration().skippable()) {
                        Set<State> r = reachability.get(current.getKey());
                        int oldsze = r.size();
                        r.addAll(reachability.get(reachable));
                        if (oldsze != r.size())
                            changed = true;
                    }
                }
            }

        }
    }


    /**
     * initialize the region borders
     *
     * @param r
     */
    private void addRegions(Region r) {
        if (r.getDuration().getUpper() != 1) {
            reachability.get(r.getStates().get(r.getStates().size() - 1))
                    .add(r.getStates().get(0));
        }

        r.getStates().stream()
                .filter(s -> s instanceof Region)
                .forEach(s -> {
                    Region region = (Region) s;
                    addRegions(region);
                });
    }

    private void initTable() {
        for (State s : flatList) {
            reachability.put(s, new HashSet<>());
        }

        for (int i = 0; i < flatList.size() - 1; i++) {
            reachability.get(flatList.get(i)).add(flatList.get(i + 1));
        }
    }

    /**
     * Returns true if <code>to</code> can be reached directly from <code>from</code>
     *
     * @param from a {@link State} from the given {@link GeneralizedTestTable}
     * @param to   a {@link State} from the given {@link GeneralizedTestTable}
     * @return signals the direct reachability
     * @throws NullPointerException if from is not from the given {@link GeneralizedTestTable}
     */
    public boolean isReachable(State from, State to) {
        return reachability.get(from).contains(to);
    }

    /**
     * @return
     */
    public List<State> getStates() {
        return flatList;
    }

    /**
     * Returns true, if the given {@link State} <code>s</code> is active at start.
     *
     * @param s a {@link State} from the {@link GeneralizedTestTable}
     * @return
     */
    public boolean isInitialReachable(State s) {
        for (State a : flatList) {
            if (a.equals(s)) return true;
            if (!a.getDuration().skippable()) return false;
        }
        return false;
    }

    /**
     *
     * @param incoming
     * @return
     */
    public Stream<State> getOutgoing(State incoming) {
        return reachability.entrySet().stream().map(
                e -> e.getValue().contains(incoming) ? e.getKey() : null
        ).filter(a -> a != null);

    }
}
