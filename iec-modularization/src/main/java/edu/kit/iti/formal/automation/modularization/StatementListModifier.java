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

// Precondition: No case statements
public abstract class StatementListModifier extends AstVisitor<Object> {

	private final boolean              _createNew;
	private final Stack<StatementList> _stmtLists = new Stack<>();

	protected StatementListModifier(final boolean createNew) {
		_createNew = createNew;
	}

	protected final void _addToCurrentList(final Statement stmt) {
		assert _stmtLists.peek() != null;
		_stmtLists.peek().add(stmt);
	}

	protected void _onEnterFirstStatementList(final StatementList stmtList) {}

	protected void _onEnterStatementList(final StatementList stmtList) {}

	@Override
	public Object visit(final AssignmentStatement assignStmt) {
		_addToCurrentList(assignStmt);
		return super.visit(assignStmt);
	}

	@Override
	public Object visit(final FunctionBlockCallStatement fbCallStmt) {
		_addToCurrentList(fbCallStmt);
		return super.visit(fbCallStmt);
	}

	@Override
	public Object visit(final IfStatement ifStmt) {

		final IfStatement newIfStmt = new IfStatement();

		_addToCurrentList(newIfStmt);

		for(GuardedStatement i : ifStmt.getConditionalBranches())
			newIfStmt.getConditionalBranches().add(new GuardedStatement(
					i.getCondition(),
					(StatementList)i.getStatements().accept(this)));

		newIfStmt.setElseBranch(
				(StatementList)ifStmt.getElseBranch().accept(this));
		return null;
	}

	@Override
	public final Object visit(final StatementList stmtList) {

		final StatementList oldStatements = new StatementList(stmtList);

		_stmtLists.push(_createNew ? new StatementList() : stmtList);

		if(_stmtLists.size() == 1) _onEnterFirstStatementList(stmtList);
		_onEnterStatementList(stmtList);

		if(!_createNew) stmtList.clear();
		for(Statement i : oldStatements) i.accept(this);

		return _stmtLists.pop();
	}
}
