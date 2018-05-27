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
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class SelectionDivergenceBuilder extends SFCBuilder {
    private Body.SFC.SelectionDivergence xml;
    private boolean parallel = false;
    private SFCGraph.Divergence product = new SFCGraph.Divergence();

    public SelectionDivergenceBuilder(Body.SFC.SelectionDivergence divergence) {
        this.xml = divergence;
    }

    public SelectionDivergenceBuilder(Body.SFC.SelectionDivergence step, boolean parallel) {
        this.xml = step;
        this.parallel = parallel;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        registerConnections(nodes, xml.getConnectionPointIn().getConnection());
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
    public Object getProduct() {
        return product;
    }

    @Override
    public List<SFCGraph.Transition> getTransitions() {
        LinkedList<SFCGraph.Transition> linkedList = new LinkedList<>();
        for (SFCBuilder b : outgoingReference)
            linkedList.addAll(b.getTransitions());
        return linkedList;
    }
}
