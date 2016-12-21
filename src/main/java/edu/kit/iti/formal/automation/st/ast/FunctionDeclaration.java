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
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class FunctionDeclaration extends TopLevelScopeElement {
    protected String functionName;
    protected String returnTypeName;
    protected Any returnType;
    protected StatementList statements = new StatementList();

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
     * <p>Getter for the field <code>returnTypeName</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getReturnTypeName() {
        return returnTypeName;
    }

    /**
     * <p>Setter for the field <code>returnTypeName</code>.</p>
     *
     * @param returnType a {@link java.lang.String} object.
     */
    public void setReturnTypeName(String returnType) {
        this.returnTypeName = returnType;
    }

    /**
     * <p>Getter for the field <code>statements</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getStatements() {
        return statements;
    }

    /**
     * <p>Setter for the field <code>statements</code>.</p>
     *
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setStatements(StatementList statements) {
        this.statements = statements;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String getBlockName() {
        return getFunctionName();
    }

    /**
     * <p>Setter for the field <code>returnType</code>.</p>
     *
     * @param returnType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public void setReturnType(Any returnType) {
        this.returnType = returnType;
    }

    /**
     * <p>Getter for the field <code>returnType</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getReturnType() {
        return returnType;
    }
}
