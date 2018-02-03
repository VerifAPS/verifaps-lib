package edu.kit.iti.formal.automation.plcopenxml;

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

import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.plcopenxml.IECExpressions;
import edu.kit.iti.formal.automation.plcopenxml.sfc.SFCBuilder;
import edu.kit.iti.formal.automation.plcopenxml.sfc.StepBuilder;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.visitors.VFactory;

import java.util.*;

/**
 * @author weigla
 * @date 24.06.2014
 */
public class SFCGraph {
    public static SFCGraph buildGraph(List<SFCAction> actions, Map<Integer, SFCBuilder> nodes) {
        Map<String, SFCAction> actionMap = new HashMap<>();
        Queue<StepBuilder> queue = new LinkedList<>();


        for (SFCBuilder e : nodes.values()) {
            e.connect(nodes, actionMap);
            if (e instanceof StepBuilder) {
                queue.add((StepBuilder) e);
            }
        }

        for (SFCBuilder e : nodes.values()) {
            e.canonical();
        }

        SFCGraph graph = new SFCGraph();

        while (!queue.isEmpty()) {
            StepBuilder sb = queue.poll();
            Node n = sb.getProduct();
            graph.nodes.add(n);
        }
        return graph;
    }

    public void print() {
        for (Node n : nodes) {
            System.out.println(n.name);
        }
    }

    public Scope getScope() {
        return scope;
    }

    public void setScope(Scope scope) {
        this.scope = scope;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Set<Node> getNodes() {
        return nodes;
    }


    public String toDot() {
        StringBuilder sb = new StringBuilder();
        sb.append("digraph G {\n   node [shape=box]; graph [splines=ortho];\n");

        for (Node n : nodes) {
            sb.append(n.name)
                    .append("[")
                    .append(((Step) n).initial ? "color=red" : "")
                    .append("];\n");
        }

        sb.append("\n");

        for (Node a : nodes) {
            for (Transition t : a.outgoing) {
                sb.append(t.from.name).append(" -> ").append(t.to.name).append(" [xlabel=\"").
                        append(VFactory.ast2St(IECExpressions.combine(Operators.AND,t.conditions))).append("\" ];\n");
            }
        }

        sb.append("}");
        return sb.toString();
    }

    public boolean containsNode(String targetName) {
        Node n = new Node(targetName);
        return nodes.contains(n);
    }

    public Step getByName(String targetName) {
        Node node = nodes.floor(new Node(targetName));
        assert node.name.equals(targetName);
        return (Step) node;
    }


    public static class Node implements Comparable<Step> {
        public String name;
        public Set<Transition> outgoing = new HashSet<>();
        public Set<Transition> incoming = new HashSet<>();

        public Node() {
        }

        public Node(String targetName) {
            name = targetName;
        }

        @Override
        public int compareTo(Step o) {
            return name.compareTo(o.name);
        }
    }

    public static class Step extends Node {
        public boolean initial;
        public StatementList onExit, onEntry, onWhile;

    }

    public static class Convergence extends Node {
        public boolean parallel;
    }

    public static class Divergence extends Node {
        public boolean parallel;
    }

    public static class Transition {
        public List<Expression> conditions = new ArrayList<>();
        public Node from, to;

        public Transition(Node to) {
            if (to == null) {
                throw new NullPointerException();
            }
            this.to = to;
        }
    }
}
