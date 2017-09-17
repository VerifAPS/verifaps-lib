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

import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;

public class FunctionBlockLink {

	public enum State {
		NOT_CHECKED,
		NOT_EQUIVALENT,
		EQUIVALENT
	}

	private State _state = State.NOT_CHECKED;

	public final FunctionBlock   fb1;
	public final FunctionBlock   fb2;
	public final VariableMapping varMappingIn;
	public final VariableMapping varMappingOut;

	public FunctionBlockLink(
			final FunctionBlock fb1,
			final FunctionBlock fb2) {

		this.fb1           = fb1;
		this.fb2           = fb2;
		this.varMappingIn  = new VariableMapping(fb1.in,  fb2.in);
		this.varMappingOut = new VariableMapping(fb1.out, fb2.out);

		fb1.setLink(this);
		fb2.setLink(this);
	}

	public final void checkEquivalence(final SmvVerifier smvVerifier) {

		// TODO: Should be removed later
		if(!varMappingIn.fullMatch || !varMappingOut.fullMatch) {
			_state = State.NOT_EQUIVALENT;
			return;
		}
		System.out.println("check: " + fb1.name + " - " + fb2.name);
		final SMVModule module1 = fb1.asSmvModule(new HashSet<>(), "$1");
		final SMVModule module2 = fb2.asSmvModule(new HashSet<>(), "$2");

		final SMVModule mainModule     = new SMVModule();
		final List<SMVExpr> invarEquations = new LinkedList<>();

		final List<SVariable> parameters1    = new LinkedList<>();
		final List<SVariable> parameters2    = new LinkedList<>();
		final Set <SVariable> inputVariables = new HashSet<>();

		// Maps from param names of second module to input variables
		final Map<String, SVariable> commonVariables = new HashMap<>();

		// Create s-variables for all parameters of the first module. Only the
		// name differs whether they are common or not
		int commonVarIndex  = 1;
		int module1VarIndex = 1;
		for(SVariable i : module1.getModuleParameter()) {

			final boolean   common =
					varMappingIn.var2ByVar1.containsKey(i.getName());
			final SVariable sVar   = new SVariable(
					common ? "v$" + commonVarIndex++ : "v1$" + module1VarIndex++,
					i.getDatatype());

			parameters1.add(sVar);
			if(common)
				commonVariables.put(
						varMappingIn.var2ByVar1.get(i.getName()), sVar);
		}

		// Create the mapping from parameters to common s-variables for the
		// second module based on the mapping for the first module or create
		// individual variables
		int module2VarIndex = 1;
		for(SVariable i : module2.getModuleParameter())
			parameters2.add(varMappingIn.var1ByVar2.containsKey(i.getName()) ?
					commonVariables.get(i.getName()) :
					new SVariable(
							"v2$" + module2VarIndex++, i.getDatatype()));

		// Merge both parameter lists to get the input variables
		inputVariables.addAll(parameters1);
		inputVariables.addAll(parameters2);

		mainModule.setName("main");
		mainModule.getInputVars().addAll(inputVariables);

		// Add instances for both function block modules
		mainModule.getStateVars().add(new SVariable(
				"fb1", new SMVType.Module(module1.getName(), parameters1)));
		mainModule.getStateVars().add(new SVariable(
				"fb2", new SMVType.Module(module2.getName(), parameters2)));

		final Map<String, SMVType> outputTypes = new HashMap<>();

		for(SVariable i : module1.getStateVars())
			if(varMappingOut.var2ByVar1.containsKey(i.getName()))
				outputTypes.put(i.getName(), i.getDatatype());

		for(Map.Entry<String, String> i : varMappingOut.var2ByVar1.entrySet()) {

			final SMVType dataType = outputTypes.get(i.getKey());

			invarEquations.add(new SBinaryExpression(
					new SVariable("fb1." + i.getKey(),   dataType),
					SBinaryOperator.EQUAL,
					new SVariable("fb2." + i.getValue(), dataType)));
		}

		mainModule.getInvarSpec().add(
				SMVFacade.combine(SBinaryOperator.AND, invarEquations));

		final boolean result = smvVerifier.verify(
				"equiv_" + fb1.name + "-" + fb2.name + ".smv",
				mainModule, module1, module2);
		System.out.println(result);
	}

	public final State getState() {
		return _state;
	}
}
