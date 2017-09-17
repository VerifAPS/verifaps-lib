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

import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.ast.TypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;

import java.util.*;

public class ModularProver {

	private final Program _program1;
	private final Program _program2;
	private final SmvVerifier _smvVerifier =
			new SmvVerifier("nuXmv/bin/nuXmv.exe");

	private final List<FunctionBlockLink> _proofOrder  = new LinkedList<>();

	private void _addFunctionBlockLink(
			final FunctionBlock              fb1,
			final FunctionBlock              fb2,
			final Map<String, FunctionBlock> remaining1,
			final Map<String, FunctionBlock> remaining2) {

		new FunctionBlockLink(fb1, fb2);

		remaining1.remove(fb1.name);
		remaining2.remove(fb2.name);
	}

	private void _createProofOrder(final FunctionBlock fb) {
		for(FunctionBlock i : fb.cgNode.succElements) _createProofOrder(i);
		if(fb.getLink() != null) _proofOrder.add(fb.getLink());
	}

	private void _findFunctionBlockLinks() {

		final Map<String, FunctionBlock> remaining1 =
				new HashMap<>(_program1.functionBlocks);
		final Map<String, FunctionBlock> remaining2 =
				new HashMap<>(_program2.functionBlocks);

		// The main programs must be linked anyway
		_addFunctionBlockLink(
				_program1.main, _program2.main, remaining1, remaining2);

		// Math function blocks with equal names
		for(Map.Entry<String, FunctionBlock> i : remaining1.entrySet())
			if(remaining2.containsKey(i.getKey()))
				_addFunctionBlockLink(
						i.getValue(), remaining2.get(i.getKey()),
						remaining1, remaining2);
	}

	public ModularProver(
			final TopLevelElements prgm1,
			final TopLevelElements prgm2) {

		_program1 = new Program(prgm1);
		_program2 = new Program(prgm2);

		_findFunctionBlockLinks();
		_createProofOrder(_program1.main);
	}

	public final boolean start() {

		for(FunctionBlockLink i : _proofOrder) i.checkEquivalence(_smvVerifier);

		return _program1.main.getLink().getState() ==
				FunctionBlockLink.State.EQUIVALENT;
	}
}
