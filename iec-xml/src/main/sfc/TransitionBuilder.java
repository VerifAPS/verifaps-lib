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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.plcopenxml.model.SFCAction;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Connection;
import edu.kit.iti.formal.automation.st.ast.ExpressionList;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * @author weigla
 * @date 25.06.2014
 */
public class TransitionBuilder extends SFCBuilder {
    private final Body.SFC.Transition transition;
    private List<InVariableBuilder> conditions = new ArrayList<>();
    protected SFCGraph.Transition product;
    private ExpressionList conditionsList = new ExpressionList();

    public TransitionBuilder(Body.SFC.Transition t) {
        transition = t;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        for (Connection c : transition.getCondition().getConnectionPointIn().getConnection()) {
            InVariableBuilder var = (InVariableBuilder)
                    nodes.get(c.getRefLocalId().intValue());
            conditions.add(var);
        }
        registerConnections(nodes, transition.getConnectionPointIn().getConnection());


    }

    @Override
    public void canonical() {
        for (InVariableBuilder ivb : conditions)
            this.conditionsList.add(ivb.getProduct());

        /*product.from = (SFCGraph.Node) incomingReferences.get(0).getProduct();
        product.to = (SFCGraph.Node) outgoingReference.get(0).getProduct();

        product.from.outgoing.add(product);
        product.to.incoming.add(product);*/
    }


    public void removeSelection() {
        if (product.from instanceof SFCGraph.Divergence) {
            SFCGraph.Divergence div = (SFCGraph.Divergence) product.from;
            if (!div.parallel) {
                //remove edge edge from graph
                product.from.outgoing.remove(product);

                SelectionDivergenceBuilder sdb = (SelectionDivergenceBuilder) incomingReferences.get(0);

                try {
                    TransitionBuilder previousBuilder = (TransitionBuilder) sdb.incomingReferences.get(0);
                    SFCGraph.Transition previous = previousBuilder.product;

                    div.incoming.remove(previous);

                    product.from = previous.from;
                    previous.from.outgoing.remove(previous);
                    previous.from.outgoing.add(product);

                    previous.conditions.addAll(product.conditions);
                } catch (ClassCastException e) {
                    e.printStackTrace();
                }
            }
        }

        if (product.to instanceof SFCGraph.Convergence) {
            SFCGraph.Convergence conv = (SFCGraph.Convergence) product.to;
            if (!conv.parallel) {
                product.to.incoming.remove(product);


                SelectionConvergenceBuilder scb = (SelectionConvergenceBuilder) outgoingReference.get(0);
                try {
                    TransitionBuilder successorBuilder = (TransitionBuilder) scb.outgoingReference.get(0);
                    SFCGraph.Transition successor = successorBuilder.product;

                    product.to = successor.to;
                    successor.to.incoming.add(product);
                    successor.to.incoming.remove(successor);
                    product.conditions.addAll(successor.conditions);
                } catch (ClassCastException e) {
                    e.printStackTrace();
                }
            }
        }
    }

    @Override
    public boolean builtNode() {
        return false;
    }

    @Override
    public Object getProduct() {
        return product;
    }

    @Override
    public List<SFCGraph.Transition> getTransitions() {
        if (outgoingReference.size() == 0) {
            return new ArrayList<>(0);
        }

        List<SFCGraph.Transition> ta = outgoingReference.get(0).getTransitions();
        List<SFCGraph.Transition> tp = new ArrayList<>();

        for (SFCGraph.Transition t : ta) {
            SFCGraph.Transition newT = new SFCGraph.Transition(t.to);
            newT.conditions.addAll(conditionsList);
            newT.conditions.addAll(t.conditions);
            tp.add(newT);
        }
        return tp;
    }
}
