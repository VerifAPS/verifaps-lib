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

import edu.kit.iti.formal.automation.modularization.ssa.*;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelScopeElement;

import java.util.*;

public class FunctionBlock {

	public final Program owner;
	public final String name;

	public final Set<Variable> in    = new HashSet<>();
	public final Set<Variable> out   = new HashSet<>();
	public final Set<Variable> local = new HashSet<>();

	private FunctionBlockLink _link;

	public final Map<String, Variable> ssaVariables = new HashMap<>();
	public final Map<String, FunctionBlockInstance> fbInstances = new HashMap<>();
	public final List<Statement> body = new LinkedList<>();
	public final GraphNode<FunctionBlock> cgNode;

	public FunctionBlock(
			final Program              owner,
			final TopLevelScopeElement source) {

		this.owner  = owner;
		this.name   = source.getIdentifier();
		this.cgNode = new GraphNode<>(this);

		final Creator ssaCreator =
				new Creator(this, source.getLocalScope());

		if(source instanceof ProgramDeclaration) {
			((ProgramDeclaration)source).getProgramBody().accept(ssaCreator);
		} else if(source instanceof FunctionBlockDeclaration) {
			((FunctionBlockDeclaration)source).
					getFunctionBody().accept(ssaCreator);
		}

		for(Statement i : body) {
			i.computeDependencies();
			System.out.println(i.pdgNode.pred.size() + "  " + i);
		}

		for(FunctionBlockInstance i : fbInstances.values())
			for(CallSite j : i.callSites) j.computeCallSiteDependencies();

		owner.functionBlocks.put(name, this);
	}

	public final void addFunctionBlockInstance(
			final FunctionBlockInstance fbInstance) {
		fbInstances.put(fbInstance.name, fbInstance);
	}

	public final void addSsaVariable(final Variable var) {

		ssaVariables.put(var.name, var);

		if(!(var instanceof FunctionBlockVariable) && var.declaration != null) {

			if(var.declaration.isInput() || var.declaration.isInOut()) {
				in.add(var);
				new InputAssignment(this, var);
			}

			if(var.declaration.isOutput() || var.declaration.isInOut())
				out.add(var);

			if(var.declaration.isLocal()) {
				local.add(var);
				new DirectAssignment(this, var, null);
			}
		}
	}

	public final void computeDependencies() {

		final Set<FunctionBlock> depFunctionBlocks = new HashSet<>();

		for(FunctionBlockInstance i : fbInstances.values())
			depFunctionBlocks.add(owner.functionBlocks.get(i.fbName));

		for(FunctionBlock i : depFunctionBlocks) {
			cgNode  .pred.add(i.cgNode);
			i.cgNode.succ.add(cgNode);
		}

		System.out.println(name + ": " + cgNode.pred.size());
	}
}
