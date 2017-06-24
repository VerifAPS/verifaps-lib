package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version 2, rewrite to separate fn block call vs function call in expr
 */
public class FunctionCall extends Expression {
    private final IdentifierPlaceHolder<FunctionDeclaration> function = new IdentifierPlaceHolder<>();
    private List<Expression> parameters = new ArrayList<>();

    public FunctionCall() {
    }

    public FunctionCall(String fnName, Expression... expr) {
        setFunctionName(fnName);
        parameters = Arrays.asList(expr);
    }

    public FunctionCall(FunctionCall functionCall) {
        function.setIdentifier(functionCall.getFunctionName());
        function.setIdentifiedObject(functionCall.function.getIdentifiedObject());
        parameters.addAll(functionCall.parameters);
    }

    public FunctionCall(String text, List<Expression> expr) {
        setFunctionName(text);
        parameters = new ArrayList<>(expr);
    }

    public String getFunctionName() {
        return function.getIdentifier();
    }

    public void setFunctionName(String functionName) {
        function.setIdentifier(functionName);
    }

    public List<Expression> getParameters() {
        return parameters;
    }

    public void setParameters(List<Expression> parameters) {
        this.parameters = parameters;
    }

    public FunctionDeclaration getFunction() {
        return function.getIdentifiedObject();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any dataType(LocalScope localScope) {
        return function.getIdentifiedObject().returnType;
    }

    @Override
    public FunctionCall clone() {
        FunctionCall f = new FunctionCall();
        f.function.setIdentifier(this.function.getIdentifier());
        f.function.setIdentifiedObject(this.function.getIdentifiedObject());
        f.parameters = parameters.stream().map(Expression::clone)
                .collect(Collectors.toList());
        return f;
    }
}
