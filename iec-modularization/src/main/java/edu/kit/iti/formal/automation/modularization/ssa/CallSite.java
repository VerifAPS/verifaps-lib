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

public final class CallSite extends Statement {

	public final FunctionBlockInstance  instance;
	public final GraphNode<CallSite>    csNode;
	public final Map<Variable, Integer> inputSnapshot = new HashMap<>();
	public final Map<String, CallSiteAssignment> assignments = new HashMap<>();
	public final PathCondition                   pathCondition;

	public CallSite(
			final FunctionBlock owner,
			final String        instanceName,
			final PathCondition pathCondition) {

		super(owner);

		this.instance      = owner.fbInstances.get(instanceName);
		this.csNode        = new GraphNode<>(this);
		this.pathCondition = pathCondition.createSnapshot();

		final Set<String> inputVarNames = new HashSet<>();
		for(Variable i : instance.inputVars.values()) inputVarNames.add(i.name);

		for(Assignment i : _getDependencySet(inputVarNames))
			inputSnapshot.put(i.variable, i.index);

		for(FunctionBlockVariable i : instance.outputVars.values())
			assignments.put(
					i.subscriptName,
					new CallSiteAssignment(owner, i, this));

		instance.callSites.add(this);
	}

	public final void computeCallSiteDependencies() {

		final Queue<Statement> notChecked = new LinkedList<>();
		final Set<Statement>   checked    = new HashSet<>();

		notChecked.add(this);

		while(!notChecked.isEmpty()) {

			final Statement stmt = notChecked.poll();
			checked.add(stmt);

			if(stmt instanceof CallSite && stmt != this) {
				csNode                 .pred.add(((CallSite)stmt).csNode);
				((CallSite)stmt).csNode.succ.add(csNode);
			} else {
				for(GraphNode<Statement> i : stmt.pdgNode.pred)
					if(!checked.contains(i.element)) notChecked.add(i.element);
			}
		}
	}

	@Override
	public final void computeDependencies() {
		for(PathCondition.Condition i : pathCondition.conditions)
			_addDependency(Variable.CONDITION_NAME, i.condIndex);
		for(Map.Entry<Variable, Integer> i : inputSnapshot.entrySet())
			_addDependency(i.getKey(), i.getValue());
	}

	@Override
	public final String toString() {

		final StringBuilder sb = new StringBuilder();

		sb.append(instance.name).append('(');

		for(Variable i : inputSnapshot.keySet())
			sb.append(((FunctionBlockVariable)i).subscriptName).append(", ");
		sb.setLength(sb.length() - 2);

		sb.append(')');

		return sb.toString();
	}
}
