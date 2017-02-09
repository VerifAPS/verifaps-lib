package edu.kit.iti.formal.automation.testtables.model;

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

import edu.kit.iti.formal.automation.testtables.StateReachability;
import edu.kit.iti.formal.automation.testtables.report.Counterexample;
import edu.kit.iti.formal.automation.testtables.report.Message;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (08.02.17)
 */
public class CounterExampleAnalyzer {
    private final StateReachability reach;
    private final List<State> states;
    private final Message message;
    private List<Map<String, String>> ceStates = new ArrayList<>();
    private List<Map<String, String>> ceInput = new ArrayList<>();

    public CounterExampleAnalyzer(
            GeneralizedTestTable testTable,
            Message msg) {
        this.reach = testTable.getReachability();
        this.states = this.reach.getStates();
        this.message = msg;

        //making a dense counter example
        Map<String, String> lastState = new HashMap<>();
        Map<String, String> lastInput = new HashMap<>();
        for (Counterexample.Step step : msg.getCounterexample().getTrace().getStep()) {
            Map<String, String> state = new HashMap<>(lastState);
            Map<String, String> input = new HashMap<>(lastInput);

            step.getInput().forEach(a -> {
                input.put(a.getName(), a.getValue());
            });

            step.getState().forEach(a -> {
                state.put(a.getName(), a.getValue());
            });

            lastState = state;
            lastInput = input;

            ceInput.add(input);
            ceStates.add(state);
        }

        Message.Counterexample.RowMappings value =new Message.Counterexample.RowMappings();
        msg.getCounterexample().setRowMappings(value);
    }


    public List<String> run() {
        Queue<SearchNode> queue = new LinkedList<>();

        for (State s : this.states) {
            if (isTrue(0, "s" + s.getId())) {
                SearchNode sn = new SearchNode(0, s);
                queue.add(sn);
            }
        }

        while (!queue.isEmpty()) {
            SearchNode cur = queue.remove();
            int time = cur.time;
            State state = cur.state;

            if (time >= ceStates.size()) continue;

            String fwd = state.getDefForward().getName();
            String out = state.getDefOutput().getName();
            String keep = state.getDefKeep().getName();

            if (isTrue(time, keep)) {
                queue.add(new SearchNode(time + 1, state, cur));
            }

            if (isTrue(time, fwd)) {
                //include every outgoing state
                reach.getOutgoing(state).forEach(
                        r -> queue.add(new SearchNode(time + 1, r, cur))
                );
            }

            if (isFalse(time, out)) {
                //yuhuuu the counter example
                message.getCounterexample().getRowMappings().getRowMap().add(cur.getRows());
            }
        }
        return message.getCounterexample().getRowMappings().getRowMap();
    }

    private boolean isTrue(int time, String var) {
        return "TRUE".equals(getValue(time, var));
    }

    private String getValue(int time, String var) {
        var = "table." + var;
        try {
            String val = ceInput.get(time).get(var);
            if (val != null) return val;
        } catch (IndexOutOfBoundsException e) {

        }
        try {
            return ceStates.get(time).get(var);
        } catch (IndexOutOfBoundsException e1) {
        }
        return null;
    }

    private boolean isFalse(int time, String var) {
        return "FALSE".equals(getValue(time, var));
    }

    private static class SearchNode {
        final int time;
        final State state;
        final SearchNode parent;

        public SearchNode(int i, State s) {
            this(i, s, null);
        }

        public SearchNode(int time, State state, SearchNode parent) {
            this.parent = parent;
            this.state = state;
            this.time = time;
        }

        public String getRows() {
            String s = "";
            if (parent != null)
                s = parent.getRows() + ", ";
            return s + state.getId();
        }
    }
}
