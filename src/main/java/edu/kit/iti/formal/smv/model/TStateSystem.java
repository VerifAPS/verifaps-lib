package edu.kit.iti.formal.smv.model;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SMVType;

import static edu.kit.iti.formal.smv.BExpressionBuilder.*;

/**
 * @author weigl
 */
public class TStateSystem {
    protected SMVModule m = new SMVModule();
    public State init = new State();
    public String name;

    public SMVModule asModule() {
        Set<State> states = getStates();

        List<SVariable> statesX = states.stream().map(TStateSystem::toVar).collect(Collectors.toList());
        // SVariable curState = new SVariable("CURRENT_STATE", new
        // SMVType.EnumType(id));

        m.statevars.addAll(statesX);

        String initname = "X_" + init.id;
        for (SVariable v : statesX) {
            m.init.add(new SAssignment(v, initname.equals(v.name) ? SLiteral.TRUE : SLiteral.FALSE));
        }
        m.init.addAll(toAssignments(init.assignments));

        for (SVariable var : m.statevars) {
            SCaseExpression esac = new SCaseExpression();

            for (State state : states) {
                esac.addCase(expr(toVar(state)).equal().to(SLiteral.TRUE).get(), state.assignments.get(var));
            }

            esac.addCase(SLiteral.TRUE, var);
            m.next.add(new SAssignment(var, esac));
        }

        //
        HashMap<SVariable, SCaseExpression> a = new HashMap<>();
        // this writing can be optimized bynesting th ecases
        for (SVariable xvar : statesX) {
            SCaseExpression esac = new SCaseExpression();
            a.put(xvar, esac);
        }

        for (Transition t : getTransitions()) {
            SVariable from = toVar(t.outgoing);
            SVariable to = toVar(t.incoming);
            SMVExpr cond = expr(from).and().to(t.guard).get();
            a.get(to).addCase(cond, SLiteral.TRUE);
        }

        for (Entry<SVariable, SCaseExpression> e : a.entrySet()) {
            e.getValue().addCase(SLiteral.TRUE, e.getKey());
        }

        m.next.addAll(toAssignments(a));

        m.name = name;
        return m;
    }

    private Set<Transition> getTransitions() {
        Set<Transition> trans = new HashSet<>();
        for (State state : getStates()) {
            trans.addAll(state.next);
        }
        return trans;
    }

    private static SVariable toVar(State state) {
        return new SVariable("X_" + state.id, SMVType.BOOLEAN);
    }

    private static Collection<? extends SAssignment> toAssignments(Map<SVariable, ? extends SMVExpr> assignments) {
        return assignments.entrySet().stream().map(entry -> new SAssignment(entry.getKey(), entry.getValue()))
                .collect(Collectors.toList());

    }

    public Set<State> getStates() {
        Set<State> states = new HashSet<>();
        Queue<State> s = new LinkedList<>();
        s.add(init);

        while (!s.isEmpty()) {
            State cur = s.poll();
            states.add(cur);

            for (Transition t : cur.next) {
                if (!states.contains(t.incoming)) {
                    s.add(t.incoming);
                }
            }
        }
        return states;
    }
}
