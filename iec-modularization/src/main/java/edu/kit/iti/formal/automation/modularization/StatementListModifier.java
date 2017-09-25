package edu.kit.iti.formal.automation.modularization;

/*-
 * #%L
 * iec-modularization
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.Stack;

public abstract class StatementListModifier extends AstVisitor<StatementList> {

	private final Stack<StatementList> _stmtLists = new Stack<>();

	protected final void _addToCurrentList(final Statement stmt) {
		assert _stmtLists.peek() != null;
		_stmtLists.peek().add(stmt);
	}

	protected void _onEnterStatementList(final StatementList stmtList) {}

	@Override
	public StatementList visit(final AssignmentStatement assignStmt) {
		_addToCurrentList(assignStmt);
		return super.visit(assignStmt);
	}

	@Override
	public StatementList visit(final FunctionBlockCallStatement fbCallStmt) {
		_addToCurrentList(fbCallStmt);
		return super.visit(fbCallStmt);
	}

	@Override
	public StatementList visit(final IfStatement ifStmt) {

		_addToCurrentList(ifStmt);

		for(GuardedStatement i : ifStmt.getConditionalBranches()) {
			i.getCondition().accept(this);
			i.setStatements(i.getStatements().accept(this));
		}
		ifStmt.setElseBranch(ifStmt.getElseBranch().accept(this));
		return null;
	}

	@Override
	public final StatementList visit(final StatementList stmtList) {
		_stmtLists.push(new StatementList());
		_onEnterStatementList(stmtList);
		for(Statement i : stmtList) i.accept(this);
		return _stmtLists.pop();
	}
}
