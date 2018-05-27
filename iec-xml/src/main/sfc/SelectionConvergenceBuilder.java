package edu.kit.iti.formal.automation.plcopenxml.sfc;

/*-
 * #%L
 * jpox
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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.plcopenxml.model.SFCAction;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class SelectionConvergenceBuilder extends SFCBuilder {
    private final Body.SFC.SelectionConvergence step;
    private SFCGraph.Convergence node = new SFCGraph.Convergence();
    private boolean parallel = false;

    public SelectionConvergenceBuilder(Body.SFC.SelectionConvergence convergence) {
        step = convergence;
    }

    public SelectionConvergenceBuilder(Body.SFC.SelectionConvergence convergence, boolean parallel) {
        this.step = convergence;
        this.parallel = parallel;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        for (Body.SFC.SelectionConvergence.ConnectionPointIn cpi : step.getConnectionPointIn())
            registerConnections(nodes, cpi.getConnection());
    }

    @Override
    public void canonical() {
        //outgoingReference = StepBuilder.insertTransitions(this);
    }

    @Override
    public boolean builtNode() {
        return parallel;
    }

    @Override
    public SFCGraph.Convergence getProduct() {
        return node;
    }

    @Override
    public List<SFCGraph.Transition> getTransitions() {
        LinkedList<SFCGraph.Transition> l = new LinkedList<>();
        for (SFCBuilder b : outgoingReference) {
            l.addAll(b.getTransitions());
        }
        return l;
    }
}
