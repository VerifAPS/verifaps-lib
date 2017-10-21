package edu.kit.iti.formal.automation.modularization.transform;

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

import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.List;
import java.util.ListIterator;

public final class CtrlStatementNormalizer extends AstVisitor<Object> {

	private Expression _caseExpression = null;

	private final StatementList _aggregateToElseBranch(
			final GuardedStatement guardedStmt,
			final StatementList    elseBranch) {

		final IfStatement newIfStmt = new IfStatement();

		newIfStmt.addGuardedCommand(guardedStmt);
		newIfStmt.setElseBranch    (elseBranch);

		return new StatementList(newIfStmt);
	}

	private final StatementList _aggregateToElseBranch(
			final Expression    condition,
			final StatementList thenBranch,
			final StatementList elseBranch) {

		final GuardedStatement guardedStmt = new GuardedStatement();

		guardedStmt.setCondition (condition);
		guardedStmt.setStatements(thenBranch);

		return _aggregateToElseBranch(guardedStmt, elseBranch);
	}

	private final BinaryExpression _createRangeExpression(
			final Literal start,
			final Literal stop) {

		return start == stop ?
				new BinaryExpression(
						_caseExpression, start, Operators.EQUALS) :
				new BinaryExpression(
					new BinaryExpression(
							_caseExpression, start, Operators.GREATER_EQUALS),
					new BinaryExpression(
							_caseExpression, stop,  Operators.LESS_EQUALS),
					Operators.AND);
	}

	@Override
	public final Object visit(final AssignmentStatement assignStmt) {
		return assignStmt;
	}

	@Override
	public final Object visit(final CaseCondition.Enumeration enumCond) {
		return _createRangeExpression(enumCond.getStart(), enumCond.getStop());
	}

	@Override
	public final Object visit(final CaseCondition.IntegerCondition intCond) {
		return new BinaryExpression(
				_caseExpression, intCond.getValue(), Operators.EQUALS);
	}

	@Override
	public final Object visit(final CaseCondition.Range rangeCond) {
		return _createRangeExpression(
				rangeCond.getStart(), rangeCond.getStop());
	}

	@Override
	public final Object visit(final CaseStatement caseStmt) {

		StatementList                 curElseStmt = caseStmt.getElseCase();
		final ListIterator<CaseStatement.Case> li =
				caseStmt.getCases().listIterator(caseStmt.getCases().size());

		_caseExpression = caseStmt.getExpression();

		while(li.hasPrevious()) {

			final CaseStatement.Case          branch = li.previous();
			final ListIterator<CaseCondition> liCond =
					branch.getConditions().listIterator();

			// Normalize the branch statements first
			branch.getStatements().accept(this);

			Expression branchCondition =
					(Expression)liCond.next().accept(this);
			while(liCond.hasNext())
				branchCondition = new BinaryExpression(
						branchCondition,
						(Expression)liCond.next().accept(this),
						Operators.OR);

			curElseStmt = _aggregateToElseBranch(
					branchCondition, branch.getStatements(), curElseStmt);
		}

		return curElseStmt.get(0);
	}

	@Override
	public final Object visit(final InvocationStatement fcCallStmt) {
		return fcCallStmt;
	}

	@Override
	public final Object visit(final IfStatement ifStmt) {

		// normalize all branches first
		super.visit(ifStmt);

		final List<GuardedStatement> branches = ifStmt.getConditionalBranches();
		StatementList             curElseStmt = ifStmt.getElseBranch();

		for(int i = branches.size() - 1; i > 0; i--)
			curElseStmt = _aggregateToElseBranch(branches.get(i), curElseStmt);
		ifStmt.setElseBranch(curElseStmt);

		return ifStmt;
	}

	@Override
	public final Object visit(final StatementList stmts) {
		for(int i = 0; i < stmts.size(); i++)
			stmts.set(i, (Statement)stmts.get(i).accept(this));
		return null;
	}
}
