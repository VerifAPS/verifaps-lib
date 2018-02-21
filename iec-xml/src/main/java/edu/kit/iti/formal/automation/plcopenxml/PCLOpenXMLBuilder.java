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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.sfclang.ast.ActionDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation;
import edu.kit.iti.formal.automation.st.ast.*;
import org.jdom2.*;
import org.jdom2.filter.Filters;
import org.jdom2.input.SAXBuilder;
import org.jdom2.input.sax.SAXHandler;
import org.jdom2.input.sax.SAXHandlerFactory;
import org.jdom2.xpath.XPathExpression;
import org.jdom2.xpath.XPathFactory;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by weigl on 23/06/14.
 */
public class PCLOpenXMLBuilder {
    /**
     * This handler ignores namespaces!
     */
    private static final SAXHandlerFactory FACTORY = new SAXHandlerFactory() {
        @Override
        public SAXHandler createSAXHandler(JDOMFactory factory) {
            return new SAXHandler() {
                @Override
                public void startElement(
                        String namespaceURI, String localName, String qName, Attributes atts)
                        throws SAXException {
                    super.startElement("", localName, qName, atts);
                }

                @Override
                public void startPrefixMapping(String prefix, String uri) throws SAXException {
                    return;
                }
            };
        }
    };
    private static XPathFactory xpathFactory = XPathFactory.instance();
    private final File filename;
    private Document document;

    public PCLOpenXMLBuilder(File filename) {
        this.filename = filename;
    }

    private static Map<String, ActionDeclaration> buildActions(Element e) {
        Map<String, ActionDeclaration> map = new LinkedHashMap<>();
        XPathExpression<Element> actions = xpathFactory.compile("./actions/action", Filters.element());
        List<Element> elements = actions.evaluate(e);
        for (Element action : elements) {
            ActionDeclaration ad = buildAction(action);
            map.put(ad.getName(), ad);
        }
        return map;
    }

    private static ActionDeclaration buildAction(Element action) {
        ActionDeclaration ad = new ActionDeclaration();
        ad.setName(action.getAttributeValue("name"));
        ad.setStBody(buildSTForPOU(action));
        ad.setSfcBody(buildSFCForPOU(action));
        return ad;
    }

    private static TopLevelElement buildPOU(Element e) {
        switch (e.getAttributeValue("pouType")) {
            case "functionBlock":
                return buildFunctionBlock(e);
            case "program":
                return buildProgram(e);
            case "function":
                return buildFunction(e);
        }
        return null;
    }

    private static FunctionDeclaration buildFunction(Element e) {
        FunctionDeclaration fd = new FunctionDeclaration();
        fd.setName(e.getAttributeValue("name"));
        fd.setScope(new InterfaceBuilder(e.getChild("interface")).get());
        fd.setStBody(buildSTForPOU(e));
        //TODO how to find the return type fd.setReturnType();
        return fd;
    }

    private static FunctionBlockDeclaration buildFunctionBlock(Element e) {
        FunctionBlockDeclaration pd = new FunctionBlockDeclaration();
        pd.setName(e.getAttributeValue("name"));
        pd.setScope(new InterfaceBuilder(e.getChild("interface")).get());
        pd.setStBody(buildSTForPOU(e));
        pd.setSfcBody(buildSFCForPOU(e));
        pd.setActions(buildActions(e));
        return pd;
    }

    private static ProgramDeclaration buildProgram(Element e) {
        ProgramDeclaration pd = new ProgramDeclaration();
        pd.setProgramName(e.getAttributeValue("name"));
        pd.setScope(new InterfaceBuilder(e.getChild("interface"))
                .get());
        pd.setStBody(buildSTForPOU(e));
        pd.setSfcBody(buildSFCForPOU(e));
        pd.setActions(buildActions(e));
        return pd;
    }

    private static SFCImplementation buildSFCForPOU(Element e) {
        XPathExpression<Element> getSTBody = xpathFactory.compile("./body/SFC", Filters.element());
        Element sfcElement = getSTBody.evaluateFirst(e);
        if (sfcElement != null) {
            return new SFCFactory(sfcElement).get();
        }
        return null;
    }

    private static StatementList buildSTForPOU(Element e) {
        XPathExpression<Text> getSTBody = xpathFactory.compile("./body/ST/xhtml/text()", Filters.text());
        Text code = getSTBody.evaluateFirst(e);
        if (code != null) {
            return IEC61131Facade.statements(code.getText());
        }
        return null;
    }

    protected Document loadXml() throws IOException, JDOMException {
        SAXBuilder saxBuilder = new SAXBuilder();
        saxBuilder.setSAXHandlerFactory(FACTORY);
        return saxBuilder.build(filename);
    }

    public TopLevelElements build() throws JDOMException, IOException {
        document = loadXml();
        document.getRootElement().setNamespace(Namespace.NO_NAMESPACE);
        TopLevelElements ast = new TopLevelElements();
        for (Element e : getPOUs()) {
            ast.add(buildPOU(e));
        }
        return ast;
    }

    public Iterable<? extends Element> getPOUs() {
        XPathExpression<Element> e = xpathFactory.compile("//pou", Filters.element());
        return e.evaluate(document);

    }
}
