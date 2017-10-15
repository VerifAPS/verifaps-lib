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
import edu.kit.iti.formal.automation.st.ast.FunctionBlockCallStatement;
import edu.kit.iti.formal.automation.st.ast.Statement;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.*;

public final class FunctionBlockInstance {

	public final class CallSite {

		private CallSiteLink _link = null;

		public final int                        id;
		public final FunctionBlockCallStatement fbCallStmt;
		public final FunctionBlockInstance      instance;
		public final GraphNode<CallSite>        csNode;
		public final VariableDeclaration        activationBit;

		public CallSite(final FunctionBlockCallStatement fbCallStmt) {

			this.id            = callSites.size();
			this.fbCallStmt    = fbCallStmt;
			this.instance      = FunctionBlockInstance.this;
			this.csNode        = new GraphNode<>(this);
			this.activationBit = new VariableDeclaration(
					name + "$act$" + id,
					VariableDeclaration.OUTPUT,
					AnyBit.BOOL);

			instance .callSites.add(this);
			caller.ir.callSites.put(fbCallStmt, this);
		}

		public final void computeDependencies() {

			final IntermediateRepresentation  ir         = instance.caller.ir;
			final Queue<GraphNode<Statement>> notChecked = new LinkedList<>();
			final Set  <GraphNode<Statement>> checked    = new HashSet<>();

			final GraphNode<Statement> firstNode = ir.pdg.get(fbCallStmt);
			notChecked.add(firstNode);

			while(!notChecked.isEmpty()) {

				final GraphNode<Statement> node = notChecked.poll();
				checked.add(node);

				if(node != firstNode &&
						node.element instanceof FunctionBlockCallStatement) {
					csNode.addPredecessor(
							ir.callSites.get(node.element).csNode);
				} else {
					for(GraphNode<Statement> i : node.pred)
						if(!checked.contains(i)) notChecked.add(i);
				}
			}
		}

		public final CallSiteLink getLink() {
			return _link;
		}

		public final void setLink(CallSiteLink link) {
			assert _link == null;
			_link = link;
		}
	}

	private FunctionBlockInstanceLink _link;

	public final String              name;
	public final VariableDeclaration declaration;
	public final FunctionBlock       type;
	public final FunctionBlock       caller;

	// Useful for call site alignment computation
	public final List<CallSite> callSites = new LinkedList<>();

	public FunctionBlockInstance(
			final VariableDeclaration declaration,
			final FunctionBlock       type,
			final FunctionBlock       caller) {

		this.name        = declaration.getName();
		this.declaration = declaration;
		this.type        = type;
		this.caller      = caller;

		caller.fbInstances.put(name, this);
	}

	public final FunctionBlockInstanceLink getLink() {
		return _link;
	}

	public final void setLink(final FunctionBlockInstanceLink link) {
		assert _link == null;
		_link = link;
	}
}
