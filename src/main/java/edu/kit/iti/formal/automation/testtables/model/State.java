package edu.kit.iti.formal.automation.testtables.model;

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

import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import lombok.Data;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (10.12.16)
 */
@Data
public class State extends TableNode {
    private final List<SMVExpr> inputExpr = new ArrayList<>();
    private final List<SMVExpr> outputExpr = new ArrayList<>();
    private final Set<State> incoming = new HashSet<>();
    private final Set<State> outgoing = new HashSet<>();
    /**
     *
     */
    private final SVariable defInput;
    /**
     *
     */
    private final SVariable defFailed;
    /**
     *
     */
    private final SVariable defForward;
    /**
     *
     */
    private final SVariable defOutput;
    /**
     * The predicate that allows keeping in this state.
     * Only necessary iff duration is DET_WAIT.
     */
    private final SVariable defKeep;
    private List<AutomatonState> automataStates;
    private boolean initialReachable;
    private boolean endState;

    public State(int id) {
        super(id);
        defOutput = new SVariable("s" + id + "_out", SMVType.BOOLEAN);
        defForward = new SVariable("s" + id + "_fwd", SMVType.BOOLEAN);
        defFailed = new SVariable("s" + id + "_fail", SMVType.BOOLEAN);
        defInput = new SVariable("s" + id + "_in", SMVType.BOOLEAN);
        defKeep = new SVariable("s" + id + "_keep", SMVType.BOOLEAN);
    }

    public void add(IoVariable v, SMVExpr e) {
        List<SMVExpr> a = v.getIo().equals("input") ? inputExpr : outputExpr;
        a.add(e);
    }

    @Override
    public boolean isLeaf() {
        return true;
    }

    @Override
    @SuppressWarnings("rawtypes")
    public List<TableNode> getChildren() {
        return Collections.EMPTY_LIST;
    }

    @Override
    public int count() {
        return 1;
    }

    @Override
    public List<State> flat() {
        LinkedList<State> l = new LinkedList<>();
        l.add(this);
        return l;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        State state = (State) o;

        return id == state.id;
    }

    @Override
    public int hashCode() {
        return id;
    }

    @Override
    public List<AutomatonState> getAutomataStates() {
        if (automataStates == null)
            automataStates = new ArrayList<>();

        if (automataStates.size() == 0) {
            if (duration.isDeterministicWait() || duration.isOmega()) {
                automataStates.add(new AutomatonState(1));
            } else {
                for (int i = 1; i <= duration.getBound(); i++) {
                    automataStates.add(new AutomatonState(i));
                }
            }
        }
        assert automataStates.size() != 0;
        return automataStates;
    }


    @Override
    public int depth() {
        return 0;
    }

    public class AutomatonState {
        private final Set<AutomatonState> incoming = new HashSet<>();
        private final Set<AutomatonState> outgoing = new HashSet<>();
        int count;

        public AutomatonState(int cnt) {
            count = cnt;
        }

        public boolean isOptional() {
            return count >= duration.getLower();
        }

        public boolean isFirst() {
            return count == 1;
        }

        public State getState() {
            return State.this;
        }

        public Set<AutomatonState> getIncoming() {
            return incoming;
        }

        public Set<AutomatonState> getOutgoing() {
            return outgoing;
        }

        public SVariable getSMVVariable() {
            return SVariable.create("s" + getId() + "_" + count).asBool();
        }

        public SVariable getDefForward() {
            return SVariable.create("s_%d_%d_fwd", id, count).asBool();
        }

        public SVariable getDefFailed() {
            return SVariable.create("s_%d_%d_fail", id, count).asBool();
        }

        /**
         * Returns true iff this is the automaton state that can infinitely repeated.
         *
         * @return
         */
        public boolean isUnbounded() {
            return count == duration.getBound() && duration.isUnbounded();
        }

        public boolean isStartState() {
            return isInitialReachable() && isFirst();
        }

        public boolean isEndState() {
            if (outgoing.size() == 0) {
                return true;
            } else {
                return outgoing.stream()
                        .map(s -> s.isEndState() || s.isOptional())
                        .reduce((a, b) -> a | b).orElse(false);
            }
        }
    }
}