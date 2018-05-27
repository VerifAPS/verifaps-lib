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
import edu.kit.iti.formal.automation.plcopenxml.scheme.AddData;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;
import org.w3c.dom.Attr;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import java.util.*;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class StepBuilder extends SFCBuilder {
    public static final String KEY_ON_ACTIVE = "700a583f-b4d4-43e4-8c14-629c7cd3bec8";
    Body.SFC.Step step;
    SFCGraph.Step node = new SFCGraph.Step();

    public StepBuilder(Body.SFC.Step step) {
        this.step = step;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        registerConnections(nodes, step.getConnectionPointIn().getConnection());
        node.name = step.getName();
        node.initial = step.isInitialStep();

        // TODO read out the names from addData
        try {
            node.onEntry = actions.get(node.name + "_entry").getStatements();
        } catch (NullPointerException npe) {
        }
        try {
            node.onExit = actions.get(node.name + "_exit").getStatements();
        } catch (NullPointerException npe) {
        }
        try {
            String activeName = getAttribute(KEY_ON_ACTIVE);
            if (activeName != null)
                node.onWhile = actions.get(activeName).getStatements();
        } catch (NullPointerException npe) {
        }
    }

    private String getAttribute(String keyOnActive) {
        AddData o = step.getAddData();
        AddData.Data d = o.getData().get(0);
        Element e = (Element) d.getAny();

        NodeList nl = e.getChildNodes();
        for (int i = 0; i < nl.getLength(); i++) {
            Attr guid = (Attr) nl.item(i).getAttributes().getNamedItem("guid");
            //System.out.println(guid.getValue());
            if (guid.getValue().equals(keyOnActive)) {
                //    System.out.println(nl.item(i).getTextContent());
                return nl.item(i).getTextContent().trim();
            }
        }
        return null;
    }

    public static List<SFCBuilder> insertTransitions(SFCBuilder t) {

        List<SFCBuilder> list = new ArrayList<>();
        /*for (SFCBuilder b : t.outgoingReference) {
            if (!(b instanceof TransitionBuilder)) {
                TransitionBuilder tb = new PseudoTransitionBuilder(
                        (SFCGraph.Node) t.getProduct(), (SFCGraph.Node) b.getProduct());

                b.incomingReferences.remove(t);
                b.incomingReferences.add(tb);

                list.add(tb);
            } else {
                list.add(b);
            }
        }*/
        return list;
    }

    @Override
    public void canonical() {
        //outgoingReference = insertTransitions(this);
    }

    @Override
    public boolean builtNode() {
        return true;
    }

    @Override
    public SFCGraph.Step getProduct() {
        List<SFCGraph.Transition> t = new LinkedList<>();

        for (SFCBuilder b : outgoingReference) {
            List<SFCGraph.Transition> a = b.getTransitions();

            for (SFCGraph.Transition c : a) {
                c.from = node;
            }

            t.addAll(a);
        }

        node.outgoing = new HashSet<>(t);
        return node;
    }


    public List<SFCGraph.Transition> getTransitions() {
        LinkedList<SFCGraph.Transition> l = new LinkedList<>();
        SFCGraph.Transition t = new SFCGraph.Transition(node);
        l.add(t);
        return l;
    }
}
