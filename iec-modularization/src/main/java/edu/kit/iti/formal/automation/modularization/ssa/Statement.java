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

import edu.kit.iti.formal.automation.modularization.FunctionBlock;
import edu.kit.iti.formal.automation.modularization.GraphNode;

import java.util.*;

public abstract class Statement {

	public final FunctionBlock        owner;
	public final int                  position;
	public final GraphNode<Statement> pdgNode;

	protected Statement(final FunctionBlock owner) {

		this.owner    = owner;
		this.position = owner.body.size();
		this.pdgNode  = new GraphNode<>(this);

		owner.body.add(this);
	}

	protected final void _addDependency(final Statement stmt) {
		pdgNode     .pred.add(stmt.pdgNode);
		stmt.pdgNode.succ.add(pdgNode);
	}

	protected final void _addDependency(
			final String varName,
			final int    index) {

		_addDependency(owner.ssaVariables.get(varName), index);
	}

	protected final void _addDependency(
			final Variable variable,
			final int      index) {

		final GraphNode<Statement> predNode =
				variable.assignments.get(index).pdgNode;

		pdgNode .pred.add(predNode);
		predNode.succ.add(pdgNode);
	}

	protected final Set<Assignment> _getDependencySet(
			final Collection<String> variables) {

		final Set<String>     redVariables = new HashSet<>(variables);
		final Set<Assignment> dependencies = new HashSet<>();
		final ListIterator<Statement>   li = owner.body.listIterator(position);

		while(li.hasPrevious() && !redVariables.isEmpty()) {

			final Statement stmt = li.previous();
			if(!(stmt instanceof Assignment)) continue;

			final Assignment assignStmt = (Assignment)stmt;
			final String     varName    = assignStmt.variable.name;
			if(!redVariables.contains(varName)) continue;

			dependencies.add   (assignStmt);
			redVariables.remove(varName);
		}

		return dependencies;
	}

	public abstract void computeDependencies();
}
