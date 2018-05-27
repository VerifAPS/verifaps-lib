package edu.kit.iti.formal.automation.plcopenxml;

/*-
 * #%L
 * iec-xml
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.parser.ErrorReporter;
import edu.kit.iti.formal.automation.sfclang.ast.*;
import edu.kit.iti.formal.automation.st.ast.Literal;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;
import lombok.Value;
import org.jdom2.Attribute;
import org.jdom2.Element;
import org.jdom2.Text;
import org.jdom2.filter.Filters;
import org.jdom2.xpath.XPathExpression;
import org.jdom2.xpath.XPathFactory;

import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
public class SFCFactory implements Supplier<SFCImplementation> {
    public static final String CODESYS_ON_ENTRY = "a6b08bd8-b696-47e3-9cbf-7408b61c9ff8";
    public static final String CODESYS_ON_EXIT = "a2621e18-7de3-4ea6-ae6d-89e9e0b7befd";
    private static final String CODESYS_ON_STEP = "700a583f-b4d4-43e4-8c14-629c7cd3bec8";
    private static final XPathFactory xpf = XPathFactory.instance();
    private static final XPathExpression<Element> xpathFindRootStep;
    private static final XPathExpression<Element> xpathGetLocalId;
    private static final XPathExpression<Element> xpathGetVendorData;
    private static final XPathExpression<Element> xpathGetNext;
    private static final XPathExpression<Attribute> qRefLocalId;
    private static final XPathExpression<Text> qExpression;
    private static final XPathExpression<Element> xpathFindActionsInActionBlock;

    static {
        /*
            All queries are relative to <SFC> root element.
         */
        xpathFindRootStep = xpf.compile("./step[@initialStep='true']", Filters.element());


        Map<String, Object> id = new HashMap<>();// Collections.singletonMap("id", null);
        id.put("id", 0);

        xpathGetLocalId = xpf.compile("./*[@localId=$id]",
                Filters.element(), id);

        xpathGetNext = xpf.compile("./*[connectionPointIn/connection[@refLocalId=$id]]",
                Filters.element(), id);

        xpathGetVendorData = xpf.instance().compile(".//attribute[@guid=$id]",
                Filters.element(), id);

        qRefLocalId =
                xpf.compile("./condition/connectionPointIn/connection/@refLocalId",
                        Filters.attribute());
        qExpression =
                xpf.compile(".//inVariable[@localId=$id]/expression/text()",
                        Filters.text(), id);

        xpathFindActionsInActionBlock =
                xpf.compile("./actionBlock[connectionPointIn/connection/@refLocalId=$id]/action",
                        Filters.element(), id);
    }

    private final Element sfcElement;
    private Map<String, Node> nodes = new HashMap<>();

    //private Set<SFCStep> sfcSteps = new HashSet<>();
    //private Set<SFCTransition> sfcTransition = new HashSet<>();
    private SFCImplementation sfc = new SFCImplementation();
    private SFCNetwork network = new SFCNetwork();
    private List<Node> usedTransitions = new LinkedList<>();

    public SFCFactory(Element element) {
        sfcElement = element;
    }

    private static String getVendorSpecificAttribute(Element e, String guid) {
        xpathGetVendorData.setVariable("id", guid);
        Element element = xpathGetVendorData.evaluateFirst(e);
        return element == null ? "" : element.getTextTrim();
    }

    private void traverse() {
        Element rootStep = xpathFindRootStep.evaluateFirst(sfcElement);
        XPathExpression<Element> matchAll = xpf.compile("./*", Filters.element());
        for (Element e : matchAll.evaluate(sfcElement)) {
            if (e.getName().equals("actionBlock") || e.getName().equals("inVariable"))
                continue; // Action blocks are handled later by the step conversion.
            Node n = factory(e);
            nodes.put(n.localId, n);
        }

        XPathExpression<Attribute> getConnectPoints = xpf.compile("./connectionPointIn/connection/@refLocalId", Filters.attribute());
        //resolve links
        for (Element e : matchAll.evaluate(sfcElement)) {
            if (e.getName().equals("actionBlock") || e.getName().equals("inVariable"))
                continue; // Action blocks are handled later by the step conversion.
            String idIncoming = e.getAttributeValue("localId");
            for (Attribute a : getConnectPoints.evaluate(e)) {
                String idOutgoing = a.getValue();
                Node incoming = nodes.get(idIncoming);
                Node outgoing = nodes.get(idOutgoing);

                if (incoming != null && outgoing != null) {
                    incoming.incoming.add(outgoing);
                    outgoing.outgoing.add(incoming);
                }
            }
        }
    }

    @SuppressWarnings("unchecked")
    private <T> T factory(Element e) {
        /*
        step, macroStep, transition, selectionDivergence
        selectionConvergence, simultaneousDivergence, simultaneousConvergence
         */
        switch (e.getName()) {
            case "step":
                return (T) new Step(e);
            case "transition":
                return (T) new Transition(e);
            case "selectionDivergence":
                return (T) new Divergence(e);
            case "selectionConvergence":
                return (T) new Convergence(e);
            case "simultaneousDivergence":
                return (T) new Divergence(e, true);
            case "simultaneousConvergence":
                return (T) new Convergence(e, true);
            case "jumpStep":
                return (T) new JumpStep(e);
            default:
                throw new IllegalStateException(e.getName());
        }
    }

    @Override
    public SFCImplementation get() {
        traverse();
        translate();

        // only simult. div/conv used, use the rest!
        ArrayList<Node> n = new ArrayList<>(nodes.values());
        n.removeAll(usedTransitions);
        for (Node node : n) {
            if (node instanceof Transition) {
                ((Transition) node).insertIntoNetwork();
            }
        }

        n = new ArrayList<>(nodes.values());
        n.removeAll(usedTransitions);
        //System.out.printf("%s%n", n);

        sfc.getNetworks().add(network);
        return sfc;
    }

    private void translate() {
        nodes.values().stream()
                .filter(n -> n instanceof Step)
                .map(Step.class::cast)
                .map(Step::createSFCStep)
                .forEach(network.getSteps()::add);

        nodes.values().stream()
                .filter(n -> n instanceof Divergence)
                .map(Divergence.class::cast)
                .forEach(Divergence::insertIntoNetwork);

        nodes.values().stream()
                .filter(n -> n instanceof Convergence)
                .map(Convergence.class::cast)
                .forEach(Convergence::insertIntoNetwork);
    }

    private void parseActionBlock(String localId,
                                  List<SFCStep.AssociatedAction> events) {
        xpathFindActionsInActionBlock.setVariable("id", localId);
        List<Element> actions = xpathFindActionsInActionBlock.evaluate(sfcElement);
        for (Element action : actions) {
            String qName = action.getAttributeValue("qualifier");
            SFCActionQualifier q = new SFCActionQualifier(qName);
            if (q.getQualifier().getHasTime()) {
                q.setTime(IEC61131Facade.INSTANCE.expr(action.getAttributeValue("duration")));
                //TODO support for indicator?
            }
            String var = action.getChild("reference").getAttributeValue("name");
            events.add(new SFCStep.AssociatedAction(q, var));
        }
    }

    public Set<SFCStep> nameToStep(Collection<String> steps) {
        return steps.stream().map(network::getStep)
                .filter(o -> o.isPresent())
                .map(o -> o.get())
                .collect(Collectors.toSet());
    }

    private SFCTransition createSFCTransition(List<String> fromName, List<String> toName,
                                              List<String> guardsFrom, List<String> guardsTo) {
        SFCTransition t = new SFCTransition();
        Set<SFCStep> st = nameToStep(toName);
        t.setTo(st);
        Set<SFCStep> sf = nameToStep(fromName);
        t.setFrom(sf);
        sf.forEach(s -> s.getOutgoing().add(t));
        st.forEach(s -> s.getIncoming().add(t));

        HashSet<String> guards = new HashSet<>(guardsFrom);
        guards.addAll(guardsTo);
        if (guards.size() > 0) {
            String guard = guards.stream().collect(Collectors.joining(" AND "));
            try {
                t.setGuard(IEC61131Facade.INSTANCE.expr(guard));
            } catch (ErrorReporter.IEC61131ParserException e) {
                System.err.println(guard);
                System.err.println(e.getMessage());
            }
        } else {
            t.setGuard(new Literal(AnyBit.Companion.getBOOL(), "TRUE"));
        }
        return t;
    }

    @ToString(callSuper = true)
    public class Transition extends Node {
        public String conditions;

        public Transition(Element t) {
            super(t);
            Attribute a = qRefLocalId.evaluateFirst(t);
            if (a != null) {
                qExpression.setVariable("id", a.getValue());
                Text textTrim = qExpression.evaluateFirst(sfcElement);
                conditions = textTrim.getText();
            } else {
                System.err.println("Following element does not have a transition guard:" + t);
            }
        }

        public void insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return;
            }
            assert outgoing.size() == 1;
            assert incoming.size() == 1;

            List<PseudoTransition> fromName = getTransitions(true);
            List<PseudoTransition> toName = getTransitions(false);

            assert outgoing.size() == toName.size();
            //assert incoming.size() == fromName.size();

            for (PseudoTransition from : fromName) {
                usedTransitions.addAll(from.usedNodes);
                for (PseudoTransition to : toName) {
                    createSFCTransition(from.getSteps(), to.getSteps(), from.guards, to.guards);
                    usedTransitions.addAll(to.usedNodes);
                }
            }
        }


        @Override
        public List<PseudoTransition> getTransitions(boolean incdirection) {
            Set<Node> ref = incdirection? incoming:outgoing;
            if (ref.size() == 0)
                System.err.println("Transition " + this + " does not have an incoming or outgoing connection");
            return ref.stream().flatMap(s -> s.getTransitions(incdirection).stream())
                    .map(pt -> {
                        pt.addGuard(conditions);
                        pt.usedNodes.add(this);
                        return pt;
                    })
                    .collect(Collectors.toList());
        }
    }

    @EqualsAndHashCode(of = "localId")
    @ToString(exclude = {"outgoing", "incoming"})
    public class Node implements Comparable<Step> {
        public Element entry;
        public String name;
        public Set<Node> outgoing = new HashSet<>();
        public Set<Node> incoming = new HashSet<>();
        public String localId;

        public Node(Element e) {
            localId = e.getAttributeValue("localId");
            name = e.getAttributeValue("name");
            assert localId != null : "@localId was not given in " + e.toString();
        }

        @Override
        public int compareTo(Step o) {
            return name.compareTo(o.name);
        }

        public List<Element> getNext() {
            xpathGetNext.setVariable("id", localId);
            return xpathGetNext.evaluate(sfcElement);
        }

        public List<PseudoTransition> getTransitions(boolean incoming) {
            return Collections.emptyList();
        }

        public Set<String> getSteps(Function<Node, Set<Node>> direction) {
            Set<String> stepsFrom = new HashSet<>();
            Queue<Node> queue = new LinkedList<>();
            queue.addAll(direction.apply(this));
            while (!queue.isEmpty()) {
                Node n = queue.remove();
                if (n instanceof Step) {
                    stepsFrom.add(n.name);
                } else {
                    if (n instanceof JumpStep) {
                        stepsFrom.add(((JumpStep) n).jumpTo);
                    } else {
                        queue.addAll(direction.apply(n));
                    }
                }
            }
            return stepsFrom;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            if (!super.equals(o)) return false;

            Node node = (Node) o;

            return localId.equals(node.localId);
        }

        @Override
        public int hashCode() {
            int result = super.hashCode();
            result = 31 * result + localId.hashCode();
            return result;
        }

        @Value
        class PseudoTransition {
            private List<String> steps = new ArrayList<>(5);
            private List<String> guards = new ArrayList<>(5);
            private Set<Node> usedNodes = new HashSet<>(5);

            public PseudoTransition(String name, String conditions, Node used) {
                this(name, used);
                guards.add(conditions);
            }

            public PseudoTransition(PseudoTransition pt) {
                steps.addAll(pt.steps);
                guards.addAll(pt.guards);
                usedNodes.addAll(pt.usedNodes);
            }

            public PseudoTransition(String name, Node usedNode) {
                this(usedNode);
                steps.add(name);
            }

            public PseudoTransition(Node used) {
                usedNodes.add(used);
            }

            public void addGuard(String conditions) {
                guards.add(conditions);
            }
        }
    }

    @ToString(callSuper = true)
    public class JumpStep extends Node {
        public String jumpTo;

        public JumpStep(Element e) {
            super(e);
            jumpTo = e.getAttributeValue("targetName");
        }

        @Override
        public List<PseudoTransition> getTransitions(boolean incoming) {
            return Collections.singletonList(new PseudoTransition(jumpTo, this));
        }
    }

    @ToString(callSuper = true)
    public class Step extends Node {
        public boolean initial;
        public String onExit, onEntry, onWhile;

        public Step(Element e) {
            super(e);
            onWhile = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
            onEntry = getVendorSpecificAttribute(e, CODESYS_ON_ENTRY);
            onExit = getVendorSpecificAttribute(e, CODESYS_ON_EXIT);

            String initialStep = e.getAttributeValue("initialStep");
            initial = initialStep != null && Boolean.valueOf(initialStep);
            //TODO onExit = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
            //TODO onEntry = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
        }

        @Override
        public List<PseudoTransition> getTransitions(boolean incoming) {
            return Collections.singletonList(new PseudoTransition(name, this));
        }

        public SFCStep createSFCStep() {
            SFCStep ss = new SFCStep();
            ss.setInitial(initial);
            ss.setName(name);
            parseActionBlock(localId, ss.getEvents());

            if (onWhile != null && !onWhile.isEmpty())
                ss.getEvents().add(new SFCStep.AssociatedAction(SFCActionQualifier.Companion.getNON_STORED(), onWhile));

            if (onExit != null && !onExit.isEmpty())
                ss.getEvents().add(new SFCStep.AssociatedAction(SFCActionQualifier.Companion.getFALLING(), onExit));

            if (onEntry != null && !onEntry.isEmpty())
                ss.getEvents().add(new SFCStep.AssociatedAction(SFCActionQualifier.Companion.getRAISING(), onEntry));

            return ss;
        }
    }

    @ToString(callSuper = true)
    public class Convergence extends Node {
        public boolean parallel;

        public Convergence(Element e) {
            super(e);
        }

        public Convergence(Element e, boolean b) {
            super(e);
            parallel = true;
        }

        @Override
        public List<PseudoTransition> getTransitions(boolean inc) {
            Set<Node> ref = inc ? incoming : outgoing;
            if (parallel) {
                if (inc) {
                    PseudoTransition pt = new PseudoTransition(this);
                    for (Node n : ref) {
                        for (PseudoTransition p : n.getTransitions(inc)) {
                            pt.steps.addAll(p.steps);
                            pt.guards.addAll(p.guards);
                            pt.usedNodes.addAll(p.usedNodes);
                        }
                    }
                    return Collections.singletonList(pt);
                }
            }
            return ref.stream()
                    .flatMap(n -> n.getTransitions(inc).stream())
                    .map(pt -> {
                        pt.usedNodes.add(this);
                        return pt;
                    })
                    .collect(Collectors.toList());
        }

        public void insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return;
            }
            // joining the edge
            //assert incoming.stream().allMatch(s -> s instanceof Transition);
            //assert outgoing.stream().allMatch(s -> s instanceof Transition);
            assert outgoing.size() == 1;

            List<PseudoTransition> fromName = getTransitions(true);
            List<PseudoTransition> toName = getTransitions(false);

            assert parallel || fromName.size() >= incoming.size();
            assert toName.size() >= outgoing.size();

            for (PseudoTransition from : fromName) {
                usedTransitions.addAll(from.usedNodes);
                for (PseudoTransition to : toName) {
                    createSFCTransition(from.getSteps(), to.getSteps(), from.guards, to.guards);
                    usedTransitions.addAll(to.usedNodes);
                }
            }
        }
    }

    @ToString(callSuper = true)
    public class Divergence extends Node {
        public boolean parallel;

        public Divergence(Element e) {
            this(e, false);
        }

        public Divergence(Element e, boolean b) {
            super(e);
            parallel = b;
        }

        @Override
        public List<PseudoTransition> getTransitions(boolean incdirection) {
            Set<Node> ref = incdirection ? incoming : outgoing;
            if (parallel && !incdirection) {
                PseudoTransition pt = new PseudoTransition(this);
                for (Node n : ref) {
                    for (PseudoTransition p : n.getTransitions(incdirection)) {
                        pt.steps.addAll(p.steps);
                        pt.guards.addAll(p.guards);
                    }
                }
                return Collections.singletonList(pt);
            }
            return ref.stream()
                    .flatMap(n -> n.getTransitions(incdirection).stream())
                    .map(pt -> {
                        pt.usedNodes.add(this);
                        return pt;
                    })
                    .collect(Collectors.toList());
        }


        public void insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return;
            }

            // splitting the edge!
            //assert outgoing.stream().allMatch(s -> s instanceof Transition);
            //assert incoming.stream().allMatch(s -> s instanceof Transition);
            assert outgoing.size() >= 1;
            assert incoming.size() == 1;

            List<PseudoTransition> fromName = getTransitions(true);
            List<PseudoTransition> toName = getTransitions(false);

            assert parallel || outgoing.size() <= toName.size();
            assert incoming.size() <= fromName.size();

            for (PseudoTransition from : fromName) {
                usedTransitions.addAll(from.usedNodes);
                for (PseudoTransition to : toName) {
                    createSFCTransition(from.getSteps(), to.getSteps(), from.guards, to.guards);
                    usedTransitions.addAll(to.usedNodes);
                }
            }


        }
    }
}