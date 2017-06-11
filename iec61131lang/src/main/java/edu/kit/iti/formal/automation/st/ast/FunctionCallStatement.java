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

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class FunctionCallStatement extends Statement {
    private FunctionCall functionCall;

    /**
     * <p>Constructor for FunctionCallStatement.</p>
     *
     * @param fc a {@link edu.kit.iti.formal.automation.st.ast.FunctionCall} object.
     */
    public FunctionCallStatement(FunctionCall fc) {
        this.functionCall = fc;
    }

    /**
     * <p>Getter for the field <code>functionCall</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.FunctionCall} object.
     */
    public FunctionCall getFunctionCall() {
        return functionCall;
    }

    /**
     * <p>Setter for the field <code>functionCall</code>.</p>
     *
     * @param functionCall a {@link edu.kit.iti.formal.automation.st.ast.FunctionCall} object.
     */
    public void setFunctionCall(FunctionCall functionCall) {
        this.functionCall = functionCall;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public FunctionCallStatement clone() {
        return new FunctionCallStatement(functionCall.clone());
    }
}
