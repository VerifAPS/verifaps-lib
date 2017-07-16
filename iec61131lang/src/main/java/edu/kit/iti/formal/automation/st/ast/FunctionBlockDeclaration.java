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
import lombok.EqualsAndHashCode;
import lombok.ToString;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@EqualsAndHashCode
@ToString
public class FunctionBlockDeclaration extends TopLevelScopeElement {
    private StatementList functionBody = new StatementList();
    private String functionBlockName;

    /**
     * <p>Getter for the field <code>functionBlockName</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getFunctionBlockName() {
        return functionBlockName;
    }

    /**
     * <p>Setter for the field <code>functionBlockName</code>.</p>
     *
     * @param functionBlockName a {@link java.lang.String} object.
     */
    public void setFunctionBlockName(String functionBlockName) {
        this.functionBlockName = functionBlockName;
    }

    /**
     * <p>Getter for the field <code>functionBody</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getFunctionBody() {
        return functionBody;
    }

    /**
     * <p>Setter for the field <code>functionBody</code>.</p>
     *
     * @param functionBody a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setFunctionBody(StatementList functionBody) {
        this.functionBody = functionBody;
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
    public String getIdentifier() {
        return getFunctionBlockName();
    }

    @Override
    public FunctionBlockDeclaration copy() {
        FunctionBlockDeclaration fb = new FunctionBlockDeclaration();
        fb.setRuleContext(getRuleContext());
        fb.functionBlockName = functionBlockName;
        fb.functionBody = functionBody.copy();
        return fb;
    }
}
