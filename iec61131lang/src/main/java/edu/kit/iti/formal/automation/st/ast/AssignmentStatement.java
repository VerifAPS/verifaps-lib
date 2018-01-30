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

import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;

/**
 * <ul>
 * <li>2: 27.02.2017: added reference attribute</li>
 * <li>Version 1: 11.06.14</li>
 * </ul>
 *
 * @author weigl, Augusto Modanese
 * @version 2
 */
@Data
public class AssignmentStatement extends Statement {
    private Reference location;
    private Expression expression;
    private boolean reference;
    private boolean assignmentAttempt;

    public AssignmentStatement() {
    }

    public AssignmentStatement(Reference variable, Expression expression) {
        this.location= variable;
        this.expression = expression;
    }


    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public boolean isReference() {
        return reference;
    }

    public AssignmentStatement setReference(boolean reference) {
        this.reference = reference;
        return this;
    }

    @Override
    public AssignmentStatement copy() {
        AssignmentStatement a = new AssignmentStatement(
                Utils.copyNull(location),
                Utils.copyNull(expression));
        a.setReference(reference);
        a.setAssignmentAttempt(assignmentAttempt);
        a.setRuleContext(getRuleContext());
        return a;
    }
}
