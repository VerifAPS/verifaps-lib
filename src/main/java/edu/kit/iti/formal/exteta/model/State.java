package edu.kit.iti.formal.exteta.model;

import edu.kit.iti.formal.exteta.schema.IoVariable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by weigl on 10.12.16.
 */
public class State {
    private final int id;
    private final List<SMVExpr> inputExpr = new ArrayList<>();
    private final List<SMVExpr> outputExpr = new ArrayList<>();
    private Duration duration = new Duration(1,1);

    public State(int id) {
        this.id = id;
    }

    public Duration getDuration() {
        return duration;
    }

    public void setDuration(Duration duration) {
        this.duration = duration;
    }

    public List<SMVExpr> getInputExpr() {
        return inputExpr;
    }

    public List<SMVExpr> getOutputExpr() {
        return outputExpr;
    }

    public void add(IoVariable v, SMVExpr e) {
        List<SMVExpr> a = v.getIo().equals("input") ? inputExpr : outputExpr;
        a.add(e);
    }

    public SVariable getSMVVariable() {
        return new SVariable("s" + id, SMVType.BOOLEAN);
    }

    public int count() {
        return 1;
    }

    public int getId() {
        return id;
    }

    public List<State> flat() {
        LinkedList<State> l = new LinkedList<>();
        l.add(this);
        return l;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        State state = (State) o;

        return id == state.id;
    }

    @Override
    public int hashCode() {
        return id;
    }

    public SVariable getDefForward() {
        return new SVariable("s" + id + "_fwd", SMVType.BOOLEAN);
    }

    public SVariable getDefKeep() {
        return new SVariable("s" + id + "_keep", SMVType.BOOLEAN);
    }

    public SVariable getDefInput() {
        return new SVariable("s" + id + "_in", SMVType.BOOLEAN);
    }

    public SVariable getDefOutput() {
        return new SVariable("s" + id + "_out", SMVType.BOOLEAN);
    }
}
