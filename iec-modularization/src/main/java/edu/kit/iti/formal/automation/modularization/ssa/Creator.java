package edu.kit.iti.formal.automation.modularization.ssa;

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

import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.modularization.FunctionBlock;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;

import java.util.*;

public final class Creator extends DefaultVisitor<Object> {

	private final PathCondition _curPathCond = new PathCondition();
	private final Variable      _condVariable;

	public final FunctionBlock owner;

	private Map<String, Integer> _createSnapshot() {

		final Map<String, Integer> snapshot = new HashMap<>();
		for(Variable i : owner.ssaVariables.values())
			snapshot.put(i.name, i.getLatestIndex());

		return snapshot;
	}

	private Map<String, Integer> _getDifSnapshot(
			final Map<String, Integer> prev) {

		final Map<String, Integer> snapshot = new HashMap<>();

		for(Variable i : owner.ssaVariables.values())
			if(i.getLatestIndex() > prev.get(i.name))
				snapshot.put(i.name, i.getLatestIndex());

		return snapshot;
	}

	private Variable _getSsaVariable(final String name) {
		return owner.ssaVariables.get(name);
	}

	public Creator(
			final FunctionBlock owner,
			final LocalScope    scope) {

		this.owner         = owner;
		this._condVariable = new Variable(owner, null);

		for(VariableDeclaration i : scope) {
			if(i.getDataType() instanceof FunctionBlockDataType) {
				new FunctionBlockInstance(owner, i);
			} else {
				new Variable(owner, i);
			}
		}
		owner.addSsaVariable(_condVariable);
	}

	@Override
	public final Object visit(final AssignmentStatement assignStmt) {

		final SymbolicReference ref =
				(SymbolicReference)assignStmt.getLocation();

		Variable var;

		if(ref.getSub() != null) {

			final String instName  = ref.getIdentifier();
			final String paramName =
					((SymbolicReference)ref.getSub()).getIdentifier();

			var = owner.fbInstances.get(instName).inputVars.get(paramName);

		} else {
			var = _getSsaVariable(ref.getIdentifier());
		}

		return new DirectAssignment(owner, var, assignStmt.getExpression());
	}

	@Override
	public final Object visit(final FunctionBlockCallStatement fbCallStmt) {

		final String                instName = fbCallStmt.getCalleeName();
		final FunctionBlockInstance instance = owner.fbInstances.get(instName);

		fbCallStmt.getInputParameters().forEach((param) ->
			new DirectAssignment(
					owner,
					instance.inputVars.get(param.getName()),
					param.getExpression()));

		return new CallSite(owner, instName, _curPathCond);
	}

	@Override
	public final Object visit(final GuardedStatement guardedStmt) {

		new DirectAssignment(owner, _condVariable, guardedStmt.getCondition());
		_curPathCond.push(_condVariable.getLatestIndex());

		guardedStmt.getStatements().accept(this);

		return null;
	}

	@Override
	public final Object visit(final IfStatement ifStmt) {

		final List<GuardedStatement> branches = ifStmt.getConditionalBranches();
		final Map<String, Integer>   initSnapshot = _createSnapshot();

		final Map<GuardedStatement, Map<String, Integer>> prevSnapshots =
				new HashMap<>();
		final Map<GuardedStatement, Map<String, Integer>> difSnapshots =
				new HashMap<>();

		// Create the SSA variables for each branch and store snapshots of the
		// currently assigned variables
		for(GuardedStatement i : branches) {
			prevSnapshots.put(i, _createSnapshot());
			i.accept(this);
			_curPathCond.switchToElseBranch();
			difSnapshots.put(i, _getDifSnapshot(prevSnapshots.get(i)));
		}
		ifStmt.getElseBranch().accept(this);

		final ListIterator<GuardedStatement> li =
				branches.listIterator(branches.size());

		// Iterate the branches reverse
		while(li.hasPrevious()) {

			final GuardedStatement     branch    = li.previous();
			final Map<String, Integer> branchDif = difSnapshots.get(branch);

			// Remove the last condition such that the the phi variables belong
			// to else branch of the surrounding condition
			_curPathCond.pop();

			// Iterate all SSA variables that have changed in the branch and/or
			// in the else-part
			for(String i :
					_getDifSnapshot(prevSnapshots.get(branch)).keySet()) {

				// Ignore the condition variables
				if(i.equals(Variable.CONDITION_NAME)) continue;

				final int initIndex = initSnapshot.get(i);
				int indexTrue, indexFalse;

				// Compute the indices that are merged within a phi node
				if(branchDif.containsKey(i)) {

					final int latestIndex =
							_getSsaVariable(i).getLatestIndex();

					indexTrue  = branchDif.get(i);
					indexFalse =
							latestIndex > indexTrue ? latestIndex : initIndex;

				} else {
					indexTrue  = initIndex;
					indexFalse = _getSsaVariable(i).getLatestIndex();
				}

				new PhiNode(
						owner,
						_getSsaVariable(i),
						branchDif.get(Variable.CONDITION_NAME),
						indexTrue, indexFalse);
			}
		}

		return null;
	}

	@Override
	public final Object visit(final StatementList stmts) {
		for(edu.kit.iti.formal.automation.st.ast.Statement i : stmts)
			i.accept(this);
		return null;
	}
}
