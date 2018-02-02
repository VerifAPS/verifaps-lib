package edu.kit.iti.formal.automation.testtables.model;

import lombok.Data;
import lombok.RequiredArgsConstructor;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
@Data
@RequiredArgsConstructor
public abstract class TableNode {
    protected final int id;
    protected Duration duration = new Duration(1, 1);

    public abstract boolean isLeaf();

    public abstract List<TableNode> getChildren();

    public abstract int count();

    public abstract List<State> flat();

    public abstract int depth();

    public abstract List<State.AutomatonState> getAutomataStates();
}