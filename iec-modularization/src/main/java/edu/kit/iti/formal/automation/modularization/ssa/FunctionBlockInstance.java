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
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.*;

public class FunctionBlockInstance {

	public final String                name;
	public final String                fbName;
	public final Map<String, FunctionBlockVariable> inputVars  = new HashMap<>();
	public final Map<String, FunctionBlockVariable> outputVars = new HashMap<>();
	public final List<CallSite> callSites = new LinkedList<>();

	public FunctionBlockInstance(
			final FunctionBlock       owner,
			final VariableDeclaration declaration) {

		final FunctionBlockDeclaration fb =
				((FunctionBlockDataType)declaration.getDataType()).
						getFunctionBlock();

		name   = declaration.getName();
		fbName = fb.getFunctionBlockName();

		owner.addFunctionBlockInstance(this);

		for(VariableDeclaration i : fb.getLocalScope()) {

			if(!i.isInput() && !i.isOutput() && !i.isInOut()) continue;

			final FunctionBlockVariable var =
					new FunctionBlockVariable(owner, i, this);

			if(i.isInput()  || i.isInOut())
				inputVars .put(var.subscriptName, var);
			if(i.isOutput() || i.isInOut())
				outputVars.put(var.subscriptName, var);
		}
	}
}
