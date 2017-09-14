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

public final class PhiNode extends Assignment {

	public final int condIndex; // Name is Variable.CONDITION_NAME
	public final int indexTrue;
	public final int indexFalse;

	public PhiNode(
			final FunctionBlock owner,
			final Variable      variable,
			final int           condIndex,
			final int           indexTrue,
			final int           indexFalse) {

		super(owner, variable);

		this.condIndex  = condIndex;
		this.indexTrue  = indexTrue;
		this.indexFalse = indexFalse;
	}

	@Override
	public final void computeDependencies() {
		_addDependency(Variable.CONDITION_NAME, condIndex);
		_addDependency(variable,                indexTrue);
		_addDependency(variable,                indexFalse);
	}

	@Override
	public final String toString() {
		return variable.toString(index) + " := " +
				owner.ssaVariables.get(Variable.CONDITION_NAME).
						toString(condIndex) +
				" ? " + variable.toString(indexTrue) +
				" : " + variable.toString(indexFalse);
	}
}
