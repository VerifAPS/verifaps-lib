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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class IfStatement extends Statement {
    private List<GuardedStatement> conditionalBranches = new ArrayList<>();
    private StatementList elseBranch = new StatementList();

    public GuardedStatement addGuardedCommand(Expression expr, StatementList statements) {
        if (expr == null)
            throw new IllegalArgumentException();

        GuardedStatement e = new GuardedStatement(expr, statements);
        conditionalBranches.add(e);
        return e;
    }

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void addGuardedCommand(GuardedStatement gc) {
        conditionalBranches.add(gc);
    }


    @Override
    public IfStatement copy() {
        IfStatement is = new IfStatement();
        conditionalBranches.forEach(gs -> is.addGuardedCommand(gs.copy()));
        is.setElseBranch(elseBranch.copy());
        return is;
    }
}
