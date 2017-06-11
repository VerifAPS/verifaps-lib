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
import edu.kit.iti.formal.automation.plcopenxml.scheme.Connection;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 *
 * Created on 26.06.2014
 * @author Alexander Weigl
 * @version 2
 */
public abstract class SFCBuilder {
    protected List<SFCBuilder> incomingReferences = new ArrayList<>();
    protected List<SFCBuilder> outgoingReference = new ArrayList<>();

    /**
     * Each edu.kit.iti.structuredtext.plcopenxml.builder initialize it's product
     * and can connect with other SFCBuilder
     *
     * @param nodes
     * @param actions
     */
    public abstract void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions);

    /**
     * Each SFCBuilder is allowed to request others products
     * Draw connections and so on
     */
    public abstract void canonical();

    public abstract boolean builtNode();

    public abstract Object getProduct();

    protected void register(Map<Integer, SFCBuilder> nodes, List<Integer> incoming) {
        for (Integer i : incoming) {
            incomingReferences.add(nodes.get(i));
            nodes.get(i).outgoingReference.add(this);
        }
    }

    protected void registerConnections(Map<Integer, SFCBuilder> nodes,
                                       List<Connection> connections) {
        List<Integer> list = new ArrayList<>();
        for (Connection c : connections) {
            list.add(c.getRefLocalId().intValue());
        }
        register(nodes, list);
    }

    public void addIncoming(SFCBuilder bldr) {
        incomingReferences.add(bldr);
    }

    public void addOutgoing(SFCBuilder bldr) {
        outgoingReference.add(bldr);
    }


    public abstract List<SFCGraph.Transition> getTransitions();
}
