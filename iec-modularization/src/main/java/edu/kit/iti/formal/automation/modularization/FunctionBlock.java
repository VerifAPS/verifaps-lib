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

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.modularization.transform.FunctionCallParamRemover;
import edu.kit.iti.formal.automation.modularization.transform.TimerToCounter;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class FunctionBlock {

	private final Set<VariableDeclaration> _tempFbInstances = new HashSet<>();
	private       FunctionBlockLink        _link;

	public final Program                    program;
	public final String                     name;
	public final StatementList              body;
	public final IntermediateRepresentation ir;
	public final GraphNode<FunctionBlock>   cgNode;
	public final String                     srcString;

	public final InlinedFunctionBlock inlinedAll;
	public final InlinedFunctionBlock inlinedAbstracted;

	public final Map<String, VariableDeclaration>   in          = new HashMap<>();
	public final Map<String, VariableDeclaration>   out         = new HashMap<>();
	public final Map<String, VariableDeclaration>   local       = new HashMap<>();
	public final Map<String, FunctionBlockInstance> fbInstances = new HashMap<>();

	public FunctionBlock(
			final Program              program,
			final TopLevelScopeElement source) {

		final StructuredTextPrinter stp = new StructuredTextPrinter();
		source.accept(stp);

		this.program   = program;
		this.name      = source.getIdentifier();
		this.ir        = new IntermediateRepresentation(this);
		this.cgNode    = new GraphNode<>(this);
		this.srcString = stp.getString();
		this.inlinedAll        = new InlinedFunctionBlock(this, null);
		this.inlinedAbstracted = new InlinedFunctionBlock(this, null);

		StatementList body = null;
		if(source instanceof ProgramDeclaration)
			body = ((ProgramDeclaration)source).getProgramBody();
		if(source instanceof FunctionBlockDeclaration)
			body = ((FunctionBlockDeclaration)source).getFunctionBody();
		assert body != null;

		this.body = body;

		// Process all variables except for the function block instances, as
		// those cannot be resolved at this point
		for(VariableDeclaration i : source.getLocalScope()) {
			if(i.getDataType() instanceof FunctionBlockDataType) {
				_tempFbInstances.add(i);
			} else if(i.isInput()) {
				in.put(i.getName(), i);
			} else if(i.isOutput()) {
				out.put(i.getName(), i);
			} else {
				local.put(i.getName(), i);
			}
		}

		program.functionBlocks.put(name, this);
	}

	public final void createIR() {

		for(VariableDeclaration i : _tempFbInstances) {
			final FunctionBlockInstance fbInstance = new FunctionBlockInstance(
					i,
					program.functionBlocks.get(
							i.getTypeDeclaration().getTypeName()),
					this);
			cgNode.addSuccessor(fbInstance.type.cgNode);
		}

		ir.create(body);
	}

	public final FunctionBlockLink getLink(){
		return _link;
	}

	public final void setLink(final FunctionBlockLink link) {
		assert _link == null;
		_link = link;
	}
}
