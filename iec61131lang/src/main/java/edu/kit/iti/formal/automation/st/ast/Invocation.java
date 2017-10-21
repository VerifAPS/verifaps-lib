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
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version 3, adapt function call as invocation
 */
@Data
@EqualsAndHashCode
@ToString
public class Invocation extends Expression {
    private final IdentifierPlaceHolder<Invocable> callee = new IdentifierPlaceHolder<>();
    private List<Parameter> parameters = new ArrayList<>();

    public Invocation() {
    }

    public Invocation(String calleeName) {
        setCalleeName(calleeName);
    }

    public Invocation(String calleeName, Expression... expr) {
        setCalleeName(calleeName);
        for (Expression e : expr) {
            parameters.add(new Parameter(e));
        }
    }

    public Invocation(Invocation invocation) {
        callee.setIdentifier(invocation.getCalleeName());
        callee.setIdentifiedObject(invocation.callee.getIdentifiedObject());
        parameters.addAll(invocation.parameters);
    }

    public Invocation(String calleeName, List<Expression> expr) {
        setCalleeName(calleeName);
        for (Expression e : expr) {
            parameters.add(new Parameter(e));
        }
    }

    public void addParameters(List<Parameter> parameterList) {
        parameters.addAll(parameterList);
    }

    public void addExpressionParameters(List<Expression> expressionList) {
        expressionList.forEach(e -> parameters.add(new Parameter(e)));
    }

    public List<Parameter> getInputParameters() {
        return parameters.stream().filter(p -> p.isInput()).collect(Collectors.toList());
    }

    public List<Parameter> getOutputParameters() {
        return parameters.stream().filter(p -> p.isOutput()).collect(Collectors.toList());
    }

    public String getCalleeName() {
        return callee.getIdentifier();
    }

    public void setCalleeName(String calleeName) {
        callee.setIdentifier(calleeName);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any dataType(LocalScope localScope) {
        return callee.getIdentifiedObject().getReturnType();
    }

    @Override
    public Expression copy() {
        Invocation fc = new Invocation();
        fc.setRuleContext(getRuleContext());
        fc.setCalleeName(getCalleeName());
        fc.setParameters(new ArrayList<>(parameters));
        return fc;

    }

    @Data
    @EqualsAndHashCode
    @ToString
    public static class Parameter
            extends Top<IEC61131Parser.Param_assignmentContext> {
        private String name;
        private boolean output;
        private Expression expression;

        public Parameter() {
        }

        public Parameter(String name, boolean output, Expression expression) {
            this.name = name;
            this.output = output;
            this.expression = expression;
        }

        public Parameter(Expression expr) {
            this(null, false, expr);
        }

        public boolean isInput() {
            return !output;
        }

        @Override
        public Parameter copy() {
            return new Parameter(name, output, expression.copy());
        }

        @Override
        public <T> T accept(Visitor<T> visitor) {
            return visitor.visit(this);
        }
    }
}
