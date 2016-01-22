package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * @author weigla
 * @date 04.07.2014
 */
public class TopLevelElements extends ArrayList<TopLevelElement> {
    public TopLevelElements(int initialCapacity) {
        super(initialCapacity);
    }

    public TopLevelElements() {
    }

    public TopLevelElements(Collection<? extends TopLevelElement> c) {
        super(c);
    }

    public <T> List<T> visit(Visitor<T> sev) {
        LinkedList<T> l = new LinkedList<>();

        for (TopLevelElement e : this)
            l.add(e.visit(sev));

        return l;
    }
}
