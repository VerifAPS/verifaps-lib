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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCAction;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class InVariableBuilder extends SFCBuilder {
    Body.SFC.InVariable variable;
    private Expression product;


    public InVariableBuilder(Body.SFC.InVariable variable) {
        this.variable = variable;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        product = IEC61131Facade.expr(variable.getExpression());
    }

    @Override
    public void canonical() {

    }

    @Override
    public boolean builtNode() {
        return false;
    }

    @Override
    public Expression getProduct() {
        return product;
    }

    @Override
    public List<SFCGraph.Transition> getTransitions() {
        return new LinkedList<>();

    }
}
