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

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.smv.ast.SMVModule;

import java.util.*;

public class FunctionBlock {

	private final Set<VariableDeclaration> _tempFbInstances = new HashSet<>();
	private       FunctionBlockLink        _link;

	public final Program                    program;
	public final String                     name;
	public final StatementList              body;
	public final IntermediateRepresentation ir;
	public final GraphNode<FunctionBlock>   cgNode;

	public final Set<VariableDeclaration> in    = new HashSet<>();
	public final Set<VariableDeclaration> out   = new HashSet<>();
	public final Set<VariableDeclaration> local = new HashSet<>();
	public final Map<String, FunctionBlockInstance> fbInstances = new HashMap<>();

	private final void _addAbstractedVariables(
			final String     prefix,
			final LocalScope dstScope) {

		_addInlinedVariables(prefix, dstScope, out, VariableDeclaration.INPUT);
	}

	private final void _addInlinedVariables(
			final String     prefix,
			final LocalScope dstScope) {

		_addInlinedVariables(prefix, dstScope, in,    VariableDeclaration.LOCAL);
		_addInlinedVariables(prefix, dstScope, out,   VariableDeclaration.LOCAL);
		_addInlinedVariables(prefix, dstScope, local, VariableDeclaration.LOCAL);

		for(FunctionBlockInstance i : fbInstances.values())
			i.type._addInlinedVariables(
					prefix + i.getName() + '$', dstScope);
	}

	private final void _addInlinedVariables(
			final String                   prefix,
			final LocalScope               dstScope,
			final Set<VariableDeclaration> variables,
			final int                      type) {

		for(VariableDeclaration i : variables) {

			final VariableDeclaration newVar = new VariableDeclaration(i);

			newVar  .setName(prefix + i.getName());
			newVar  .setType(type);
			dstScope.add    (newVar);
		}
	}

	public FunctionBlock(
			final Program              program,
			final TopLevelScopeElement source) {

		this.program = program;
		this.name    = source.getIdentifier();
		this.ir      = new IntermediateRepresentation(this);
		this.cgNode  = new GraphNode<>(this);

		StatementList body = null;

		if(source instanceof ProgramDeclaration)
			body = ((ProgramDeclaration)      source).getProgramBody();
		if(source instanceof FunctionBlockDeclaration)
			body = ((FunctionBlockDeclaration)source).getFunctionBody();

		this.body = body;

		// Process all variables except for the function block instances, as
		// those cannot be resolved at this point
		for(VariableDeclaration i : source.getLocalScope()) {
			if(i.getDataType() instanceof FunctionBlockDataType) {
				_tempFbInstances.add(i);
			} else if(i.isInput()) {
				in.add(i);
			} else if(i.isOutput()) {
				out.add(i);
			} else {
				local.add(i);
			}
		}

		program.functionBlocks.put(name, this);
	}

	public final void createIR() {

		for(VariableDeclaration i : _tempFbInstances) {
			final FunctionBlockInstance fbInstance = new FunctionBlockInstance(
					i,
					program.functionBlocks.get(
							i.getTypeDeclaration().getTypeName()),
					this);
			cgNode.addSuccessor(fbInstance.type.cgNode);
		}

		ir.create(body);
	}

	public final FunctionBlockLink getLink(){
		return _link;
	}

	public final void inline(
			final String        prefix,
			final StatementList dstBody) {

		final SmvPreparator smvPreparator =
				new SmvPreparator(ir, prefix, dstBody);

		for(Statement i : body) i.accept(smvPreparator);
	}

	public final boolean isAbstractionPossible() {
		return _link != null &&
				_link.getState() == FunctionBlockLink.State.EQUIVALENT;
	}

	public final void setLink(final FunctionBlockLink link) {
		_link = link;
	}

	public final SMVModule asSmvModule(
			final Set<FunctionBlockInstance> abstractedInstances,
			final String                     suffix) {

		final ProgramDeclaration programDecl = new ProgramDeclaration();
		final LocalScope         dstScope    = programDecl.getLocalScope();

		programDecl.setProgramName(name);

		_addInlinedVariables("", dstScope, in,    VariableDeclaration.INPUT);
		_addInlinedVariables("", dstScope, out,   VariableDeclaration.OUTPUT);
		_addInlinedVariables("", dstScope, local, VariableDeclaration.LOCAL);

		for(FunctionBlockInstance i : fbInstances.values()) {
			if(abstractedInstances.contains(i)) {
				i.type._addAbstractedVariables(i.getName() + '$', dstScope);
			} else {
				i.type._addInlinedVariables(i.getName() + '$', dstScope);
			}
		}

		inline("", programDecl.getProgramBody());

		final SMVModule module = SymbExFacade.evaluateProgram(
				programDecl, program.typeDeclarations);

		module.setName(module.getName() + suffix);

		return module;
	}
}
