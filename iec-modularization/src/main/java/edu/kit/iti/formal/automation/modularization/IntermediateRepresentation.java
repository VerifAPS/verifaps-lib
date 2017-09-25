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

import java.util.*;

public final class IntermediateRepresentation extends AstVisitor<Object> {

	private final class Scope {

		private final Scope                                  _parent;
		private final GraphNode<Statement>                   _ctrlNode;
		private final Map<String, Set<GraphNode<Statement>>> _assignments =
				new HashMap<>();

		private Scope(final GraphNode<Statement> ctrlNode) {
			_parent   = _curScope;
			_ctrlNode = ctrlNode;
			_curScope = this;
		}

		private Set<GraphNode<Statement>> _getAssignments(final String variable) {
			if(_assignments.containsKey(variable)) {
				return _assignments.get(variable);
			} else if(_parent != null) {
				return _parent._getAssignments(variable);
			} else {
				return new HashSet<>();
			}
		}

		private Set<GraphNode<Statement>> _getAssignmentSet(
				final String variable) {

			if(!_assignments.containsKey(variable))
				_assignments.put(variable, new HashSet<>());

			return _assignments.get(variable);
		}

		private void _exit() {
			_curScope = _parent;
		}
	}

	private static final class ReferenceCorrector extends AstVisitor<Object> {

		@Override
		public final Object visit(final SymbolicReference symbRef) {

			final SymbolicReference sub = (SymbolicReference) symbRef.getSub();

			if(sub != null) {
				symbRef.setIdentifier(
						symbRef.getIdentifier() + '$' + sub.getIdentifier());
				symbRef.setSub(null);
			}

			return null;
		}
	}

	private GraphNode<Statement> _curNode;
	private Scope                _curScope = new Scope(null);

	public final FunctionBlock        functionBlock;
	public final GraphNode<Statement> outputGuard = new GraphNode<>(null);

	public final Map<Statement, GraphNode<Statement>> pdg = new HashMap<>();

	public final Map<FunctionBlockCallStatement, FunctionBlockInstance.CallSite>
			callSites = new HashMap<>();

	private GraphNode<Statement> _createNode(final Statement statement) {

		_curNode = new GraphNode<>(statement);

		if(_curScope._ctrlNode != null)
			_curNode.addPredecessor(_curScope._ctrlNode);
		pdg.put(statement, _curNode);

		return _curNode;
	}

	private void _readFrom(final String variable) {
		_curNode.addPredecessors(_curScope._getAssignments(variable));
	}

	private void _writeTo(final String variable) {

		final Set<GraphNode<Statement>> assignmentSet =
				_curScope._getAssignmentSet(variable);

		assignmentSet.clear();
		assignmentSet.add(_curNode);
	}

	public IntermediateRepresentation(final FunctionBlock functionBlock) {
		this.functionBlock = functionBlock;
	}

	public final void create(final StatementList body) {

		body.accept(new ReferenceCorrector());
		body.accept(this);

		// Initialize the output guard node that can be used to create a slice
		// containing the whole function block
		_curNode = outputGuard;
		for(VariableDeclaration i : functionBlock.out.values())
			_readFrom(i.getName());
	}

	@Override
	public final Object visit(final AssignmentStatement assignStmt) {

		_createNode(assignStmt);
		assignStmt.getExpression().accept(this);
		_writeTo(((SymbolicReference)assignStmt.getLocation()).getIdentifier());

		return null;
	}

	@Override
	public final Object visit(final FunctionBlockCallStatement fbCallStmt) {

		final FunctionBlockInstance          fbInstance =
				functionBlock.fbInstances.get(fbCallStmt.getCalleeName());
		final FunctionBlockInstance.CallSite callSite   =
				fbInstance.new CallSite(fbCallStmt);

		_createNode(fbCallStmt);

		for(VariableDeclaration i : fbInstance.type.in.values())
			_readFrom(fbInstance.name + '$' + i.getName());

		for(VariableDeclaration i : fbInstance.type.out.values())
			_writeTo(fbInstance.name + '$' + i.getName());

		callSite.computeDependencies();
		return null;
	}

	@Override
	public final Object visit(final IfStatement ifStmt) {

		if(ifStmt.getConditionalBranches().size() > 1) {

			final IfStatement            newIfStmt = new IfStatement();
			final List<GuardedStatement> branches  =
					ifStmt.getConditionalBranches();

			newIfStmt.setConditionalBranches(
					branches.subList(1, branches.size()));
			newIfStmt.setElseBranch(ifStmt.getElseBranch());

			ifStmt.setConditionalBranches(branches.subList(0, 1));
			ifStmt.setElseBranch         (new StatementList(newIfStmt));
		}

		final GuardedStatement branch = ifStmt.getConditionalBranches().get(0);

		final GraphNode<Statement> node = _createNode(ifStmt);
		branch.getCondition().accept(this);

		final Scope scopeThen = new Scope(node);
		branch.getStatements().accept(this);
		scopeThen._exit();

		final Scope scopeElse = new Scope(node);
		ifStmt.getElseBranch().accept(this);
		scopeElse._exit();

		final Set<String> assignedVariables = new HashSet<>();
		assignedVariables.addAll(scopeThen._assignments.keySet());
		assignedVariables.addAll(scopeElse._assignments.keySet());

		for(String i : assignedVariables) {

			final Set<GraphNode<Statement>> assignThen =
					scopeThen._assignments.get(i);
			final Set<GraphNode<Statement>> assignElse =
					scopeElse._assignments.get(i);
			final Set<GraphNode<Statement>> destinationSet =
					_curScope._getAssignmentSet(i);

			if(assignThen != null && assignElse != null)
				destinationSet.clear();

			if(assignThen != null) destinationSet.addAll(assignThen);
			if(assignElse != null) destinationSet.addAll(assignElse);
		}

		return null;
	}

	@Override
	public final Object visit(final SymbolicReference symbRef) {
		_readFrom(symbRef.getIdentifier());
		return null;
	}
}
