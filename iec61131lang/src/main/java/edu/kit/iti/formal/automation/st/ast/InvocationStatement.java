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
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.util.List;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@EqualsAndHashCode
@ToString
@Data
public class InvocationStatement extends Statement {
    private Invocation invocation = new Invocation();

    public InvocationStatement(String fnName, Expression... expr) {
        invocation = new Invocation(fnName, expr);
    }

    public InvocationStatement() {
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public InvocationStatement copy() {
        InvocationStatement f = new InvocationStatement();
        f.setInvocation(invocation);
        return f;
    }

    public List<Invocation.Parameter> getParameters() {
        return invocation.getParameters();
    }

    public void setParameters(List<Invocation.Parameter> parameters) {
        invocation.setParameters(parameters);
    }

    public String getCalleeName() {
        return invocation.getCalleeName();
    }

    public void setCalleeName(String calleeName) {
        invocation.setCalleeName(calleeName);
    }

    public List<Invocation.Parameter> getInputParameters() {
        return invocation.getInputParameters();
    }

    public List<Invocation.Parameter> getOutputParameters() {
        return invocation.getOutputParameters();
    }
}
