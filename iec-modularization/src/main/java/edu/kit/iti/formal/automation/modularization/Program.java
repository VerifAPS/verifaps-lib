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
import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.*;

public final class Program {

	public final FunctionBlock              main;
	public final Map<String, FunctionBlock> functionBlocks = new HashMap<>();
	public final TypeDeclarations typeDeclarations = new TypeDeclarations();
	/*
	// returns 'true' if the link has been found
	private boolean _findLinkInCallGraph(
			final FunctionBlock        fb,
			final FunctionBlockLink    fbLink,
			final Stack<FunctionBlock> path,
			final Set<FunctionBlock>   fixed) {

		// Function blocks that are already part of the order are not visited
		// again
		if(fixed.contains(fb)) return false;

		path.push(fb);

		if(fb.getLink() == fbLink) {

			// TODO: be careful with stack iteration (order!)
			topDownOrdered.addAll(path);
			fixed         .addAll(path);
			return true;

		} else {

			for(FunctionBlock i : fb.cgNode.succElements)
				if(_findLinkInCallGraph(i, fbLink, path, fixed)) return true;
		}

		path.pop();
		return false;
	}

	private void _findLinkInCallGraph(
			final FunctionBlockLink  fbLink,
			final Set<FunctionBlock> fixed) {

		for(FunctionBlock i : fixed)
			_findLinkInCallGraph(i, fbLink, new Stack<>(), fixed);
	}
	*/
	private void _createInlinedFunctionBlock(
			final FunctionBlock                    fb,
			final AbstractionVariable.NameSelector nameSelector) {

		for(FunctionBlock i : fb.cgNode.succElements)
			_createInlinedFunctionBlock(i, nameSelector);

		// Will do nothing if is has been created before
		fb.inlinedAll.create(
				new InlinedFunctionBlock.Configuration(fb),
				null, nameSelector);
	}

	public Program(
			final TopLevelElements                 elements,
			final AbstractionVariable.NameSelector nameSelector) {

		IEC61131Facade.resolveDataTypes(elements);
		/*
		final TopLevelElements simplified = SymbExFacade.simplify(elements, false, true, true, true, true);
		final StructuredTextPrinter stp = new StructuredTextPrinter();

		for(TopLevelElement i : simplified) {
			stp.clear();
			i.accept(stp);
			System.out.println(stp.getString());
		}
		*/
		// Collect all type declarations
		for(TopLevelElement i : elements)
			if(i instanceof TypeDeclarations)
				typeDeclarations.addAll((TypeDeclarations)i);

		FunctionBlock main = null;
		for(TopLevelElement i : elements) {
			if(i instanceof ProgramDeclaration)
				main = new FunctionBlock(this, (ProgramDeclaration)i);
			if(i instanceof FunctionBlockDeclaration)
				new FunctionBlock(this, (FunctionBlockDeclaration)i);
		}
		this.main = main;

		for(FunctionBlock i : functionBlocks.values()) i.createIR();

		if(main == null)
			throw new NullPointerException("No program declaration found");

		_createInlinedFunctionBlock(main, nameSelector);
	}
}
