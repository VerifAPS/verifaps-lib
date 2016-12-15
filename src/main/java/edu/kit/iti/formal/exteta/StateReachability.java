package edu.kit.iti.formal.exteta;

import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.exteta.model.Region;
import edu.kit.iti.formal.exteta.model.State;

import java.util.*;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class StateReachability {
    private final GeneralizedTestTable gtt;
    private List<State> flatList;
    Map<State, Set<State>> reachability = new HashMap<>();

    public StateReachability(GeneralizedTestTable table) {
        gtt = table;
        flatList = gtt.getRegion().flat();
        initTable();
        addRegions(gtt.getRegion());
        fixpoint();
    }


    private void fixpoint() {
        boolean changed = true;
        while (changed) {
            changed = false;

            for (Map.Entry<State, Set<State>> current : reachability.entrySet()) {
                for (State reachable : current.getValue()) {
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
        if (!r.getDuration().isOneStep()) {
            reachability.get(r.getStates().get(0)).add(
                    r.getStates().get(r.getStates().size() - 1));
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
