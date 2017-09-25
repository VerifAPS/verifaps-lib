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

import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.*;

public final class InlinedFunctionBlock {

	private final class BodyCreator extends StatementListModifier {

		private final FunctionBlockInstance _activationInst;
		private final Configuration         _config;
		private       boolean               _rootStmtList = true;

		private BodyCreator(
				final FunctionBlockInstance activationInst,
				final Configuration         config) {

			_activationInst = activationInst;
			_config         = config;
		}

		private void _addAssignment(
				final FunctionBlockInstance.CallSite callSite,
				final String                         literal) {

			_addToCurrentList(new AssignmentStatement(
					new SymbolicReference(callSite.activationBit.getName()),
					new Literal          (AnyBit.BOOL, literal)));
		}

		@Override
		protected void _onEnterStatementList(final StatementList stmtList) {

			if(!_rootStmtList || _activationInst == null) return;

			for(FunctionBlockInstance.CallSite i : _activationInst.callSites)
				_addAssignment(i, "FALSE");

			_rootStmtList = false;
		}

		@Override
		public final StatementList visit(
				final FunctionBlockCallStatement fbCallStmt) {

			final FunctionBlockInstance.CallSite callSite =
					original.ir.callSites.get(fbCallStmt);
			final FunctionBlockInstance fbInstance        = callSite.instance;
			final InstanceState         instState         =
					_config.getState(fbInstance);

			if(fbInstance == _activationInst)
				_addAssignment(callSite, "TRUE");

			// For abstracted instances no statements need to be added
			if(instState == InstanceState.ABSTRACTED) return null;

			final PrefixAdder           prefixAdder =
					new PrefixAdder(fbInstance.name + '$');
			final InlinedFunctionBlock  inlinedFb   =
					instState == InstanceState.INLINED_ABSTRACT ?
							fbInstance.type.inlinedAbstracted :
							fbInstance.type.inlinedAll;

			for(Statement i : inlinedFb.declaration.getProgramBody()) {
				final Statement stmtCopy = i.copy();
				stmtCopy.accept(prefixAdder);
				_addToCurrentList(stmtCopy);
			}
			return null;
		}
	}

	private final class PrefixAdder extends AstVisitor<Object> {

		private final String _prefix;

		private PrefixAdder(final String prefix) {
			_prefix = prefix;
		}

		@Override
		public final Object visit(final SymbolicReference symbRef) {
			symbRef.setIdentifier(_prefix + symbRef.getIdentifier());
			return null;
		}
	}

	public enum InstanceState {
		INLINED_FULL,
		INLINED_ABSTRACT,
		ABSTRACTED
	}

	public static final class Configuration {

		private final Map<FunctionBlockInstance, InstanceState> _instStates =
				new HashMap<>();

		public Configuration(final FunctionBlock fb) {
			for(FunctionBlockInstance i : fb.fbInstances.values())
				_instStates.put(i, InstanceState.INLINED_FULL);
		}

		public final InstanceState getState(
				final FunctionBlockInstance fbInstance) {

			assert _instStates.containsKey(fbInstance);
			return _instStates.get(fbInstance);
		}

		public final void changeToAbstracted(
				final FunctionBlockInstance fbInstance) {

			assert getState(fbInstance) == InstanceState.INLINED_FULL;
			_instStates.put(fbInstance, InstanceState.ABSTRACTED);
		}

		public final void changeToInlinedAbstract(
				final FunctionBlockInstance fbInstance) {

			assert getState(fbInstance) == InstanceState.INLINED_FULL;
			_instStates.put(fbInstance, InstanceState.INLINED_ABSTRACT);
		}
	}

	private boolean _created = false;

	// provides the input and output variables
	public final FunctionBlock            original;
	public final Map<String, AbstractionVariable> abstractionVars = new HashMap<>();
	public final ProgramDeclaration declaration = new ProgramDeclaration();

	private void _addVariables(
			final String                        prefix,
			final int                           specifier,
			final Iterable<VariableDeclaration> variables) {

		for(VariableDeclaration i : variables)
			declaration.getLocalScope().add(new VariableDeclaration(
					prefix + i.getName(), specifier, i.getDataType()));
	}

	private void _useActivationAsOutput(final FunctionBlockInstance fbInst) {

		final Set<String> prefixedInputNames = new HashSet<>();

		for(String i : fbInst.type.in.keySet())
			prefixedInputNames.add(fbInst.name + "$" + i);

		for(VariableDeclaration i : declaration.getLocalScope()) {
			if(original.out.containsKey(i.getName())) {
				i.setType(VariableDeclaration.LOCAL);
			} else if(prefixedInputNames.contains(i.getName())) {
				i.setType(VariableDeclaration.OUTPUT);
			}
		}

		for(FunctionBlockInstance.CallSite i : fbInst.callSites)
			declaration.getLocalScope().add(i.activationBit);
	}

	public InlinedFunctionBlock(final FunctionBlock original) {
		this.original = original;
		this.declaration.setProgramName(original.name);
	}

	public final void create(
			final Configuration                    config,
			final FunctionBlockInstance            activatedInst,
			final AbstractionVariable.NameSelector nameSelector) {

		if(_created) return;

		// The abstraction variables are created outside as they need the
		// reference to the corresponding function block
		for(AbstractionVariable i : abstractionVars.values())
			declaration.getLocalScope().add(new VariableDeclaration(
					nameSelector.getName(i),
					VariableDeclaration.INPUT,
					i.type));

		// Add the variables of the function block itself
		_addVariables("", VariableDeclaration.INPUT,  original.in.values());
		_addVariables("", VariableDeclaration.OUTPUT, original.out.values());
		_addVariables("", VariableDeclaration.LOCAL,  original.local.values());

		// Create local variables for all inlined instances
		for(FunctionBlockInstance i : original.fbInstances.values()) {

			// The input variables are added anyway, but most could be removed
			// for abstracted instances if the code writing them is also removed
			_addVariables(
					i.name + "$", VariableDeclaration.LOCAL, i.type.in.values());

			if(config.getState(i) == InstanceState.ABSTRACTED) continue;

			_addVariables(
					i.name + "$", VariableDeclaration.LOCAL, i.type.out.values());
			_addVariables(
					i.name + "$", VariableDeclaration.LOCAL, i.type.local.values());
		}

		declaration.setProgramBody(
				original.body.accept(new BodyCreator(activatedInst, config)));

		if(activatedInst != null) _useActivationAsOutput(activatedInst);
		_created = true;
	}

	@Override
	public final String toString() {
		final StructuredTextPrinter stp = new StructuredTextPrinter();
		declaration.accept(stp);
		return stp.getString();
	}
}
