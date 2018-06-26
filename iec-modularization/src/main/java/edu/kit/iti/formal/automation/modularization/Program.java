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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.modularization.transform.CtrlStatementNormalizer;
import edu.kit.iti.formal.automation.modularization.transform.FunctionCallParamRemover;
import edu.kit.iti.formal.automation.modularization.transform.TimerToCounter;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.*;

public final class Program {

	public final FunctionBlock              main;
	public final Map<String, FunctionBlock> functionBlocks = new HashMap<>();
	public final TypeDeclarations typeDeclarations = new TypeDeclarations();

	private void _createInlinedFunctionBlock(
			final FunctionBlock                    fb,
			final AbstractionVariable.NameSelector nameSelector) {

		for(FunctionBlock i : fb.cgNode.succElements)
			_createInlinedFunctionBlock(i, nameSelector);

		// Will do nothing if is has been created before
		fb.inlinedAll.create(
				new InlinedFunctionBlock.Configuration(fb), nameSelector);
	}

	public Program(
			final PouElements elements,
			final AbstractionVariable.NameSelector nameSelector) {

		// Collect all type declarations
		for(PouElement i : elements)
			if(i instanceof TypeDeclarations)
				typeDeclarations.addAll((TypeDeclarations)i);

		// Simplify and normalize program
		for(PouElement i : elements) {

			if(!(i instanceof HasScope)) continue;

			SymbExFacade.INSTANCE.simplify(typeDeclarations, (HasScope)i,
					true,
					false,
					true,
					true);

			i.accept(new CtrlStatementNormalizer());
			i.accept(new FunctionCallParamRemover());
			i.accept(new TimerToCounter());
		}

		IEC61131Facade.INSTANCE.resolveDataTypes(elements);

		FunctionBlock main = null;
		for(PouElement i : elements) {
			if(i instanceof ProgramDeclaration) {
				main = new FunctionBlock(this, (HasScope)i);
			} else if(i instanceof FunctionBlockDeclaration) {
				new FunctionBlock(this, (HasScope)i);
			}
		}
		assert main != null;

		this.main = main;

		// Create the intermediate representations
		for(FunctionBlock i : functionBlocks.values()) i.createIR();

		_createInlinedFunctionBlock(main, nameSelector);
	}
}
