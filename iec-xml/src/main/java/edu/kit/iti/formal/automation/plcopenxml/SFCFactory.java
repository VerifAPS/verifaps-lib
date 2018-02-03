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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.sfclang.ast.SFCAction;
import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import lombok.Data;
import lombok.ToString;
import org.jdom2.Attribute;
import org.jdom2.Element;
import org.jdom2.Text;
import org.jdom2.filter.Filters;
import org.jdom2.xpath.XPathExpression;
import org.jdom2.xpath.XPathFactory;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
public class SFCFactory extends DefaultPOUBuilder implements PCLOpenXMLBuilder.Builder {
    private static final String CODESYS_ON_STEP = "700a583f-b4d4-43e4-8c14-629c7cd3bec8";
    private static final XPathExpression<Element> xpathFindRootStep;
    private static final XPathExpression<Element> xpathGetLocalId;
    private static final XPathExpression<Element> xpathGetVendorData;
    private static final XPathExpression<Element> xpathGetNext;

    static {
        xpathFindRootStep = XPathFactory.instance().compile(".//step[@initialStep='true']",
                Filters.element());
        Map<String, Object> id = new HashMap<>();// Collections.singletonMap("id", null);
        id.put("id", 0);

        xpathGetLocalId = XPathFactory.instance().compile(".//*[@localId=$id]",
                Filters.element(), id);

        xpathGetNext = XPathFactory.instance().compile(
                ".//SFC/*[connectionPointIn/connection[@refLocalId=$id]]",
                Filters.element(), id);


        xpathGetVendorData = XPathFactory.instance().compile(
                ".//attribute[@guid=$id]",
                Filters.element(), id);
    }

    Set<Node> steps = new HashSet<>();
    private FunctionBlockDeclaration decl = new FunctionBlockDeclaration();
    private SFCImplementation sfc = new SFCImplementation();

    public SFCFactory(Element element) {
        super(element);
    }

    private static String getVendorSpecificAttribute(Element e, String guid) {
        xpathGetVendorData.setVariable("id", guid);
        Element element = xpathGetVendorData.evaluateFirst(e);
        return element == null ? "" : element.getTextTrim();
    }

    @Override
    public TopLevelElements build() {
        Scope vs = parseInterface();
        decl.setSfcBody(sfc);
        parseActions();
        traverse();
        TopLevelElements tle = new TopLevelElements();
        tle.add(decl);
        return tle;
    }

    private void traverse() {
        Element rootStep = xpathFindRootStep.evaluateFirst(element);
        Step n = new Step(rootStep);
        steps.add(n);
        Queue<Node> queue = new LinkedList<>();
        queue.add(n);
        while (!queue.isEmpty()) {
            Node s = queue.remove();
            discover(s);
            for (Transition t : s.outgoing) {
                t.from = s;
                t.getNext().forEach(e -> {
                    Node to = factory(e);
                    t.to = to;
                    if (!steps.contains(to)) {
                        queue.add(to);
                        steps.add(to);
                    }
                });
            }
        }
    }

    private void discover(Node s) {
        List<Element> transitions = s.getNext();
        for (Element t : transitions) {
            Transition tr = new Transition(t);
            s.outgoing.add(tr);
        }
    }

    @SuppressWarnings("unchecked")
    private <T> T factory(Element e) {
        switch (e.getName()) {
            case "step":
                return (T) new Step(e);
            case "transition":
                return (T) new Transition(e);
            case "divergence":
                return (T) new Divergence(e);
            case "convergence":
                return (T) new Convergence(e);
            case "jumpStep":
                return (T) new JumpStep(e);
            default:
                throw new IllegalStateException(e.getName());
        }
    }

    private void parseActions() {
        XPathExpression<Element> xpath = XPathFactory.instance().compile("//action", Filters.element());
        for (Element action : xpath.evaluate(element)) {
            String name = action.getAttributeValue("name");
            String stCode = action.getChild("body").getChild("ST").getChildText("xhtml");
            SFCAction act = new SFCAction();
            act.setName(name);
            act.setStBody(IEC61131Facade.statements(stCode));
            sfc.getActions().add(act);
        }
    }


    @Data
    @ToString
    public class Node implements Comparable<Step> {
        public Element entry;
        public String name;
        public Set<Transition> outgoing = new HashSet<>();
        public Set<Transition> incoming = new HashSet<>();
        public String localId;

        public Node(Element e) {
            localId = e.getAttributeValue("localId");
            name = e.getAttributeValue("name");
        }

        @Override
        public int compareTo(Step o) {
            return name.compareTo(o.name);
        }

        public List<Element> getNext() {
            xpathGetNext.setVariable("id", localId);
            return xpathGetNext.evaluate(element);
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
    }

    public class JumpStep extends Node {
        public JumpStep(Element e) {
            super(e);
        }
    }

    @Data
    @ToString
    public class Step extends Node {
        public boolean initial;
        public String onExit, onEntry, onWhile;
        public String localId;

        public Step(Element e) {
            super(e);
            onWhile = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
            String initialStep = e.getAttributeValue("initialStep");
            initial = initialStep != null && Boolean.valueOf(initialStep);
            //TODO onExit = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
            //TODO onEntry = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
        }
    }

    public class Convergence extends Node {
        public boolean parallel;

        public Convergence(Element e) {
            super(e);
        }
    }

    public class Divergence extends Node {
        public boolean parallel;

        public Divergence(Element e) {
            super(e);
        }
    }

    @Data
    @ToString
    public class Transition extends Node {
        public String conditions;
        public Node from, to;

        public Transition(Element t) {
            super(t);

            XPathExpression<Attribute> qRefLocalId = XPathFactory.instance()
                    .compile("./condition/connectionPointIn/connection/@refLocalId",
                            Filters.attribute());
            Attribute a = qRefLocalId.evaluateFirst(t);
            XPathExpression<Text> qExpression = XPathFactory.instance()
                    .compile(".//inVariable[@localId=$id]/expression/text()",
                            Filters.text(), Collections.singletonMap("id", null));
            qExpression.setVariable("id", a.getValue());
            Text textTrim = qExpression.evaluateFirst(element);
            conditions = textTrim.getText();
        }
    }

/*
    private Map<Integer, PCLOpenXMLBuilder.Builder> parseNodes(Body.SFC child) {
        Map<Integer, PCLOpenXMLBuilder.Builder> list = new HashMap<>();
        for (Object e : child.getCommentOrErrorOrConnector()) {
            if (e instanceof Body.SFC.Transition) {
                Body.SFC.Transition d = (Body.SFC.Transition) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new TransitionBuilder(d));
            } else if (e instanceof Body.SFC.Step) {
                Body.SFC.Step d = (Body.SFC.Step) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new StepBuilder(d));
            } else if (e instanceof Body.SFC.InVariable) {
                Body.SFC.InVariable d = (Body.SFC.InVariable) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new InVariableBuilder(d));
            } else if (e instanceof Body.SFC.SelectionDivergence) {
                Body.SFC.SelectionDivergence d = (Body.SFC.SelectionDivergence) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new SelectionDivergenceBuilder(d));
            } else if (e instanceof Body.SFC.SelectionConvergence) {
                Body.SFC.SelectionConvergence d = (Body.SFC.SelectionConvergence) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new SelectionConvergenceBuilder(d));
            } else if (e instanceof Body.SFC.JumpStep) {
                Body.SFC.JumpStep d = (Body.SFC.JumpStep) e;
                Integer localId = d.getLocalId().intValue();
                list.put(localId, new JumpStepBuilder(d));
            } else {
                throw new IllegalArgumentException("SFC Node of type " + e.getClass() + " is not supported yet!");
            }
        }
        return list;
    }


    private Expression parseExpression(String expression) {
        return IEC61131Facade.expr(expression);
    }

    private List<SFCAction> parseActions(Project.Types.Pous.Pou.Actions actions) {
        ArrayList<SFCAction> l = new ArrayList<>();

        if (actions != null) {
            for (Project.Types.Pous.Pou.Actions.Action action : actions.getAction())
                l.add(parseAction(action));
        }
        return l;
    }

    private SFCAction parseAction(Project.Types.Pous.Pou.Actions.Action action) {
        String name = action.getName();
        org.w3c.dom.Element st = (org.w3c.dom.Element) action.getBody().getST().getAny();

        if (st == null) {
            throw new IllegalArgumentException("Only Actions with ST are support: Error in action: " + name);
        }

        StatementList sl = parseStatementList(st);
        return new SFCAction(name, sl);
    }


    private Any findDataType(DataType type) {
        Class<? extends DataType> clazz = type.getClass();

        for (String name : DataTypes.getDataTypeNames()) {
            try {
                Method m = clazz.getMethod("get" + name);
                Object r = m.invoke(type);
                if (r != null)
                    return DataTypes.getDataType(name);
            } catch (NoSuchMethodException | InvocationTargetException | IllegalAccessException e) {

            }
        }

        if (type.getDerived() != null) {
            throw new IllegalStateException("derived typs not handled");
            //return new DerivedType(type.getDerived().getName());
        }

        if (type.getArray() != null) {
            throw new IllegalArgumentException("An variable of array type is not yet supported!");
        }

        if (type.getStruct() != null) {
            throw new IllegalArgumentException("An variable of struct type is not yet supported!");
        }

        if (type.getSubrangeSigned() != null) {
            throw new IllegalArgumentException("An variable of subrange signed type is not yet supported!");
        }

        if (type.getSubrangeUnsigned() != null) {
            throw new IllegalArgumentException("An variable of subrange unsigned type is not yet supported!");
        }

        throw new IllegalArgumentException("An variable with unexpected type found, only ANY_INT and BOOL  allowed!");
    }


    private ScalarValue<?, ?> parseConstants(String s) {
        return (ScalarValue<?, ?>) IEC61131Facade.expr(s);
    }

    private StatementList parseStatementList(String xhtml) {
        return IEC61131Facade.statements(xhtml);
    }

    private StatementList parseStatementList(Element st) {
//        System.err.println("Parsing SL: --------------------\n"+st.getTextContent()+"\n--------------------\n");
        return parseStatementList(st.getTextContent());
    }
    */
}
