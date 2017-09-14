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

public class CallSiteAssignment extends Assignment {

	public final CallSite callSite;

	public CallSiteAssignment(
			final FunctionBlock owner,
			final FunctionBlockVariable variable,
			final CallSite callSite) {

		super(owner, variable);
		this.callSite = callSite;
	}

	@Override
	public final void computeDependencies() {
		_addDependency(callSite);
	}

	@Override
	public final String toString() {
		return "WRITE_TO(" + variable.toString(index) + ")";
	}
}
