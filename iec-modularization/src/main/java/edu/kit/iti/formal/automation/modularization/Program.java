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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.HashMap;
import java.util.Map;

public final class Program {

	public final FunctionBlock              main;
	public final Map<String, FunctionBlock> functionBlocks = new HashMap<>();

	public Program(final TopLevelElements elements) {

		IEC61131Facade.resolveDataTypes(elements);

		FunctionBlock main = null;
		for(TopLevelElement i : elements) {
			if(i instanceof ProgramDeclaration)
				main = new FunctionBlock(this, (ProgramDeclaration)i);
			if(i instanceof FunctionBlockDeclaration)
				new FunctionBlock(this, (FunctionBlockDeclaration)i);
		}
		this.main = main;

		if(main == null)
			throw new NullPointerException("No program declaration found");

		for(FunctionBlock i : functionBlocks.values()) i.computeDependencies();
	}
}
