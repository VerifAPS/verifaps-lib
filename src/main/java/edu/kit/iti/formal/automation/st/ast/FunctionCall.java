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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class FunctionCall extends Expression {
    private String functionName;
    private List<Parameter> parameters = new ArrayList<>();

    /**
     * <p>Constructor for FunctionCall.</p>
     */
    public FunctionCall() {
    }

    /**
     * <p>Constructor for FunctionCall.</p>
     *
     * @param fnName a {@link java.lang.String} object.
     * @param expr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public FunctionCall(String fnName, Expression... expr) {
        functionName = fnName;
        for (Expression e : expr) {
            parameters.add(new Parameter(e));
        }
    }

    /**
     * <p>Constructor for FunctionCall.</p>
     *
     * @param functionCall a {@link edu.kit.iti.formal.automation.st.ast.FunctionCall} object.
     */
    public FunctionCall(FunctionCall functionCall) {
        functionName = functionCall.functionName;
        parameters.addAll(functionCall.parameters);
    }

    /**
     * <p>Getter for the field <code>functionName</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getFunctionName() {
        return functionName;
    }

    /**
     * <p>Setter for the field <code>functionName</code>.</p>
     *
     * @param functionName a {@link java.lang.String} object.
     */
    public void setFunctionName(String functionName) {
        this.functionName = functionName;
    }

    /**
     * <p>addInputParameter.</p>
     *
     * @param key a {@link java.lang.String} object.
     * @param visit a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void addInputParameter(String key, Expression visit) {
        if (visit == null)
            throw new IllegalArgumentException("expression can not be null");
        parameters.add(new Parameter(key, false, visit));
    }

    /**
     * <p>addOutputParameter.</p>
     *
     * @param key a {@link java.lang.String} object.
     * @param visit a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public void addOutputParameter(String key, Reference visit) {
        assert key != null;
        assert visit != null;

        parameters.add(new Parameter(key, false, visit));
    }

    /**
     * <p>Getter for the field <code>parameters</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<Parameter> getParameters() {
        return parameters;
    }

    /**
     * <p>Setter for the field <code>parameters</code>.</p>
     *
     * @param parameters a {@link java.util.List} object.
     */
    public void setParameters(List<Parameter> parameters) {
        this.parameters = parameters;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Any dataType(LocalScope localScope) {
        return null;//TODO lookup function
    }


    public static class Parameter {
        private String name;
        private boolean output;
        private Expression expression;

        public Parameter(String name, boolean output, Expression expression) {
            this.name = name;
            this.output = output;
            this.expression = expression;
        }

        public Parameter(Expression expr) {
            this(null,false,expr);
        }


        public String getName() {
            return name;
        }

        public void setName(String name) {
            this.name = name;
        }

        public boolean isOutput() {
            return output;
        }

        public void setOutput(boolean output) {
            this.output = output;
        }

        public Expression getExpression() {
            return expression;
        }

        public void setExpression(Expression expression) {
            this.expression = expression;
        }
    }
}
