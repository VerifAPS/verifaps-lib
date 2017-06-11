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

import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
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
import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 23/06/14.
 */
public class PCLOpenXMLBuilder {
    private final File filename;
    private XPathFactory xpathFactory = XPathFactory.instance();
    private List<Builder> builders = new ArrayList<>();


    public PCLOpenXMLBuilder(File filename) {
        this.filename = filename;
    }

    protected Document loadXml() throws IOException, JDOMException {
        SAXBuilder saxBuilder = new SAXBuilder();
        saxBuilder.setSAXHandlerFactory(FACTORY);
        return saxBuilder.build(filename);
    }


    public TopLevelElements build() throws JDOMException, IOException {
        Document p = loadXml();
        p.getRootElement().setNamespace(Namespace.NO_NAMESPACE);
        addBuilders("//pou[body/SFC]", this::createSFCFactory, p);
        addBuilders("//pou[body/FB]", this::createFBFactory, p);
        addBuilders("//pou[body/ST]", this::createSTFactory, p);

        builders.forEach(Builder::build);

        return null;
    }

    private Builder createSTFactory(Element element) {
        return new STBuilder(element);
    }

    private Builder createFBFactory(Element element) {
        return new FBFactory(element);
    }

    private Builder createSFCFactory(Element element) {
        return new SFCFactory(element);
    }

    private void addBuilders(String xpath, BuilderFactory factory, Document document) {
        XPathExpression<Element> cxpath = xpathFactory.compile(xpath,
                Filters.element());
        List<Element> elements = cxpath.evaluate(document);
        elements.forEach(e -> builders.add(factory.createBuilder(e)));
    }

    interface BuilderFactory {
        Builder createBuilder(Element element);
    }

    interface Builder {
        TopLevelElement build();
    }

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
}
