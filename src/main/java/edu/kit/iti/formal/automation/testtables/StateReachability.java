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
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class StateReachability {
    private final GeneralizedTestTable gtt;
    Map<State, Set<State>> reachability = new HashMap<>();
    private List<State> flatList;

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


    private void fixpoint() {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<State, Set<State>> current : reachability.entrySet()) {
                Set<State> reachables = new HashSet<>(current.getValue());
                for (State reachable : reachables) {
                    if (reachable.getDuration().skipable()) {
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


    private void addRegions(Region r) {
        if (r.getDuration().getUpper() != 1) {
            reachability.get(r.getStates().get(r.getStates().size() - 1))
                    .add(r.getStates().get(0));
        }

        for (State s : r.getStates()) {
            if (s instanceof Region) {
                Region region = (Region) s;
                addRegions(region);
            }
        }
    }

    private void initTable() {
        for (State s : flatList) {
            reachability.put(s, new HashSet<>());
        }

        for (int i = 0; i < flatList.size() - 1; i++) {
            reachability.get(flatList.get(i)).add(flatList.get(i + 1));
        }
    }

    public boolean isReachable(State a, State b) {
        return reachability.get(a).contains(b);
    }

    public List<State> getStates() {
        return flatList;
    }

    public boolean isInitialReachable(State s) {
        for (State a : flatList) {
            if (a.equals(s)) return true;
            if (!a.getDuration().skipable()) return false;
        }
        return false;
    }

    public Stream<State> getOutgoing(State incoming) {
        return reachability.entrySet().stream().map(
                e -> e.getValue().contains(incoming) ? e.getKey() : null
        ).filter(a -> a != null);

    }
}
