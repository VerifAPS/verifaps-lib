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
import edu.kit.iti.formal.automation.st.ast.Literal;
import edu.kit.iti.formal.automation.st.ast.VariableBuilder;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import org.jdom2.Element;


/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
public abstract class DefaultPOUBuilder implements PCLOpenXMLBuilder.Builder {

    protected Element element;

    public DefaultPOUBuilder(Element element) {
        this.element = element;
    }


    public Scope parseInterface() {
        Element interfaze = element.getChild("interface");
        Scope d = new Scope();
        add(interfaze.getChild("inputVars"), d, VariableDeclaration.INPUT);
        add(interfaze.getChild("outputVars"), d, VariableDeclaration.OUTPUT);
        add(interfaze.getChild("localVars"), d, 0);
        //TODO Test for IN_OUT and others

        return d;
    }

    protected void add(Element vars, Scope d, int flags) {
        if (vars == null) {
            return;
        }

        VariableBuilder builder = d.builder();
        builder.push(flags);

        for (Element e : vars.getChildren("variable")) {
            String name = e.getAttributeValue("name");
            String datatype = getDatatype(e.getChild("type"));
            Literal initValue = getInitialValue(e.getChild("initialValue"));
            builder.identifiers(name)
                    .setInitialization(initValue)
                    .setBaseType(datatype)
                    .create();
        }
    }

    protected String getDatatype(Element e) {
        Element derived = e.getChild("derived");
        if (derived != null) {
            return derived.getAttributeValue("name");
        } else {
            return e.getChildren().get(0).getName();
        }
    }


    private Literal getInitialValue(Element initialValue) {
        if (initialValue == null)
            return null;

        Element simpleValue = initialValue.getChild("simpleValue");
        if (simpleValue == null)
            return null;

        return (Literal) IEC61131Facade.expr(simpleValue.getAttributeValue("value"));
    }

}
