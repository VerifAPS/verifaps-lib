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
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;

public final class FunctionBlockLink {

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

	private void _createAbstractionVariables(
			final InlinedFunctionBlock               dstFb1,
			final InlinedFunctionBlock               dstFb2,
			final InlinedFunctionBlock.Configuration config1) {

		for(FunctionBlockInstance i : fb1.fbInstances.values()) {
			switch(config1.getState(i)) {
				case ABSTRACTED:
					_createAbstVarsForAbstraction(dstFb1, dstFb2, i.getLink());
					break;
				case INLINED_ABSTRACT:
					_createAbstVarsForAbstractedInlining(
							dstFb1, dstFb2, i.getLink());
					break;
				case INLINED_FULL:
					break; // No abstraction variables necessary
			}
		}
	}

	private void _createAbstVarsForAbstractedInlining(
			final InlinedFunctionBlock      dstFb1,
			final InlinedFunctionBlock      dstFb2,
			final FunctionBlockInstanceLink instLink) {

		final FunctionBlockInstance inst1    = instLink.fbi1;
		final FunctionBlockInstance inst2    = instLink.fbi2;
		final InlinedFunctionBlock  inlined1 = inst1.type.inlinedAbstracted;
		final InlinedFunctionBlock  inlined2 = inst2.type.inlinedAbstracted;

		// add common abstraction variables
		for(AbstractionVariable j : inlined1.abstractionVars.values())
			if(j.isCommon())
				new AbstractionVariable(
						dstFb1, dstFb2, inst1.name, inst2.name, j);

		// add exclusive abstraction variables of first instance
		for(AbstractionVariable j : inlined1.abstractionVars.values())
			if(!j.isCommon())
				new AbstractionVariable(
						dstFb1, null, inst1.name, null, j);

		// add exclusive abstraction variables of second instance
		for(AbstractionVariable j : inlined2.abstractionVars.values())
			if(!j.isCommon())
				new AbstractionVariable(
						null, dstFb2, null, inst2.name, j);
	}

	private void _createAbstVarsForAbstraction(
			final InlinedFunctionBlock      dstFb1,
			final InlinedFunctionBlock      dstFb2,
			final FunctionBlockInstanceLink instLink) {

		final FunctionBlockInstance inst1         = instLink.fbi1;
		final FunctionBlockInstance inst2         = instLink.fbi2;
		final VariableMapping       outputMapping =
				inst1.type.getLink().varMappingOut;

		for(Map.Entry<String, String> i : outputMapping.var2ByVar1.entrySet())
			new AbstractionVariable(
					dstFb1, dstFb2,
					inst1.name + "$" + i.getKey(),
					inst2.name + "$" + i.getValue(),
					inst1.type.out.get(i.getKey()).getTypeDeclaration());

		for(String i : outputMapping.unmapped1)
			new AbstractionVariable(
					dstFb1, null, inst1.name + "$" + i, null,
					inst1.type.out.get(i).getTypeDeclaration());

		for(String i : outputMapping.unmapped2)
			new AbstractionVariable(
					null, dstFb2, null, inst2.name + "$" + i,
					inst2.type.out.get(i).getTypeDeclaration());
	}

	private SMVExpr _createEquivExpression(
			final String               name1,
			final String               name2,
			final Map<String, SMVType> types1,
			final Map<String, SMVType> types2) {

		return new SBinaryExpression(
				new SVariable("fb1." + name1, types1.get(name1)),
				SBinaryOperator.EQUAL,
				new SVariable("fb2." + name2, types2.get(name2)));
	}

	private boolean _checkEqualActivation(
			final FunctionBlockInstanceLink          instLink,
			final InlinedFunctionBlock.Configuration config1,
			final InlinedFunctionBlock.Configuration config2,
			final VariableMapping                    output,
			final SmvVerifier                        smvVerifier) {

		final InlinedFunctionBlock dstFb1 =
				new InlinedFunctionBlock(fb1, instLink.fbi1);
		final InlinedFunctionBlock dstFb2 =
				new InlinedFunctionBlock(fb2, instLink.fbi2);

		_createAbstractionVariables(dstFb1, dstFb2, config1);

		dstFb1.create(config1, AbstractionVariable::getName1);
		dstFb2.create(config2, AbstractionVariable::getName2);

		return _checkEquivalence(
				dstFb1, dstFb2, output, smvVerifier,
				"act_[" + fb1.name + "]-[" + fb2.name + "]_[" +
						instLink.fbi1.name + "]-[" + instLink.fbi2.name + "]");
	}

	private boolean _checkEquivalence(
			final InlinedFunctionBlock               dstFb1,
			final InlinedFunctionBlock               dstFb2,
			final InlinedFunctionBlock.Configuration config1,
			final InlinedFunctionBlock.Configuration config2,
			final VariableMapping                    output,
			final SmvVerifier                        smvVerifier) {

		_createAbstractionVariables(dstFb1, dstFb2, config1);

		dstFb1.create(config1, AbstractionVariable::getName1);
		dstFb2.create(config2, AbstractionVariable::getName2);

		return _checkEquivalence(
				dstFb1, dstFb2, output, smvVerifier,
				"equiv_[" + fb1.name + "]-[" + fb2.name + "]");
	}

	private boolean _checkEquivalence(
			final InlinedFunctionBlock dstFb1,
			final InlinedFunctionBlock dstFb2,
			final VariableMapping      output,
			final SmvVerifier          smvVerifier,
			final String               fileName) {

		assert (dstFb1.activatedInstance == null &&
				dstFb2.activatedInstance == null) ||
				dstFb1.activatedInstance.getLink() ==
						dstFb2.activatedInstance.getLink();

		final SMVModule moduleMain = new SMVModule();
		final SMVModule module1    = SymbExFacade.evaluateProgram(
				dstFb1.declaration, fb1.program.typeDeclarations);
		final SMVModule module2    = SymbExFacade.evaluateProgram(
				dstFb2.declaration, fb2.program.typeDeclarations);

		moduleMain.setName("main");
		module1   .setName(fb1.name + "_1");
		module2   .setName(fb2.name + "_2");

		// 'paramValues' contains the variables from the main module that are
		// written to 'paramDef'
		final List<SVariable> paramDef1    = module1.getModuleParameter();
		final List<SVariable> paramDef2    = module2.getModuleParameter();
		final int             paramCount1  = paramDef1.size();
		final int             paramCount2  = paramDef2.size();
		final List<SVariable> paramValues1 =
				new ArrayList<>(Collections.nCopies(paramCount1, null));
		final List<SVariable> paramValues2 =
				new ArrayList<>(Collections.nCopies(paramCount2, null));
		final List<SVariable> inputVars    = moduleMain.getInputVars();

		// Maps from param names of the second module to the corresponding
		// symbolic variables that have been created by the first module
		final Map<String, SVariable> commonValues = new HashMap<>();

		// Create all parameters passed to the first module
		for(int i = 0; i < paramCount1; i++) {

			final SVariable sVar     = paramDef1.get(i);
			final String    sVarName = sVar.getName();
			SVariable       newSVar  = null;

			if(varMappingIn.unmapped1.contains(sVarName)) {

				newSVar = new SVariable(
						"v1$" + sVarName, sVar.getDatatype());

			} else if(varMappingIn.var2ByVar1.containsKey(sVarName)) {

				newSVar = new SVariable(
						"c$" + inputVars.size(), sVar.getDatatype());
				commonValues.put(
						varMappingIn.var2ByVar1.get(sVarName), newSVar);

			} else if(dstFb1.abstractionVars.containsKey(sVarName)) {

				final AbstractionVariable abstVar =
						dstFb1.abstractionVars.get(sVarName);

				assert abstVar.isCommon(); // TODO: remove later
				newSVar = new SVariable(
						"a$" + inputVars.size(), sVar.getDatatype());
				commonValues.put(abstVar.name2, newSVar);
			}

			assert newSVar != null;
			paramValues1.set(i, newSVar);
			inputVars   .add(newSVar);
		}

		// Create or find all parameters passed to the second module
		for(int i = 0; i < paramCount2; i++) {

			final SVariable sVar     = paramDef2.get(i);
			final String    sVarName = sVar.getName();
			SVariable       newSVar  = commonValues.get(sVarName);

			if(newSVar == null) {

				if(varMappingIn.unmapped2.contains(sVarName))
					newSVar = new SVariable(
							"v2$" + sVarName, sVar.getDatatype());

				assert newSVar != null;
				inputVars.add(newSVar);
			}

			paramValues2.set(i, newSVar);
		}

		// Add instances for both function block modules
		moduleMain.getStateVars().add(new SVariable(
				"fb1", new SMVType.Module(module1.getName(), paramValues1)));
		moduleMain.getStateVars().add(new SVariable(
				"fb2", new SMVType.Module(module2.getName(), paramValues2)));

		// Only the state variables that considered to be output are collected
		// in this map
		final Map<String, SMVType> stateTypes1    = new HashMap<>();
		final Map<String, SMVType> stateTypes2    = new HashMap<>();
		final List<SMVExpr>        invarEquations = new LinkedList<>();

		// Store all output types
		for(SVariable i : module1.getStateVars())
			stateTypes1.put(i.getName(), i.getDatatype());
		for(SVariable i : module2.getStateVars())
			stateTypes2.put(i.getName(), i.getDatatype());

		if(dstFb1.activatedInstance != null) {

			for(FunctionBlockInstance.CallSite i :
					dstFb1.activatedInstance.callSites)
				_createActivationInvariant(
						i.getLink(), dstFb1, dstFb2, invarEquations,
						stateTypes1, stateTypes2);

		} else {

			for(Map.Entry<String, String> i : output.var2ByVar1.entrySet())
				invarEquations.add(_createEquivExpression(
						i.getKey(), i.getValue(), stateTypes1, stateTypes2));
		}

		// Aggregate all equivalence terms into a single term
		//moduleMain.getLTLSpec().add(new SQuantified(
		//		STemporalOperator.G,
		//		SMVFacade.combine(SBinaryOperator.AND, invarEquations)));
		moduleMain.getInvarSpec().add(
				SMVFacade.combine(SBinaryOperator.AND, invarEquations));

		return smvVerifier.verify(
				fileName, false, moduleMain, module1, module2);
	}

	private void _createActivationInvariant(
			final CallSiteLink         csLink,
			final InlinedFunctionBlock dstFb1,
			final InlinedFunctionBlock dstFb2,
			final List<SMVExpr>        dstEquations,
			final Map<String, SMVType> types1,
			final Map<String, SMVType> types2) {

		final InlinedFunctionBlock.Activation activation1 =
				dstFb1.activationVariables.get(csLink.cs1);
		final InlinedFunctionBlock.Activation activation2 =
				dstFb2.activationVariables.get(csLink.cs2);

		final List<SMVExpr> implyEquations = new LinkedList<>();

		dstEquations.add(_createEquivExpression(
				activation1.activationBit.getName(),
				activation2.activationBit.getName(),
				types1, types2));

		for(Map.Entry<String, String> j :
				dstFb1.activatedInstance.type.getLink().varMappingIn.var2ByVar1.entrySet())
			implyEquations.add(_createEquivExpression(
					activation1.variables.get(j.getKey()).getName(),
					activation1.variables.get(j.getValue()).getName(),
					types1, types2));

		dstEquations.add(new SBinaryExpression(
				new SVariable(
						"fb1." + activation1.activationBit.getName(),
						SMVType.BOOLEAN),
				SBinaryOperator.IMPL,
				SMVFacade.combine(SBinaryOperator.AND, implyEquations)));
	}

	private void _createInstanceLink(
			final String      instName1,
			final String      instName2,
			final Set<String> remaining1,
			final Set<String> remaining2) {

		final FunctionBlockInstance instance1 = fb1.fbInstances.get(instName1);
		final FunctionBlockInstance instance2 = fb2.fbInstances.get(instName2);

		// Right now we only want the instances to have the same amount of call
		// sites
		if(instance1.callSites.size() == instance2.callSites.size())
			new FunctionBlockInstanceLink(instance1, instance2);

		remaining1.remove(instName1);
		remaining2.remove(instName2);
	}

	private void _groupInstances(
			final Iterable<FunctionBlockInstance>           src,
			final Map<FunctionBlockLink, Pair<Set<String>>> dst,
			final Pair.Selector<Set<String>>                selector) {

		for(FunctionBlockInstance i : src) {
			final Pair<Set<String>> dstSet = dst.get(i.type.getLink());
			if(dstSet != null)
				selector.getElement(dstSet).add(i.name);
		}
	}

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

		Logging.log("Checking equivalence of [" +
				fb1.name + "," + fb2.name + "]");
		Logging.pushIndent();

		if(fb1.srcString.equals(fb2.srcString)) {

			boolean calleesEqual = true;
			for(FunctionBlock i : fb1.cgNode.succElements)
				if(!i.getLink().isEquivalent()) calleesEqual = false;

			if(calleesEqual) {

				Logging.log("Structural equivalent (no proof)");
				Logging.popIndent();

				_state = State.EQUIVALENT;
				return;
			}
		}

		final Set<GraphNode<FunctionBlockInstance.CallSite>> callSiteNodes =
				new HashSet<>();

		final InlinedFunctionBlock.Configuration config1 =
				new InlinedFunctionBlock.Configuration(fb1);
		final InlinedFunctionBlock.Configuration config2 =
				new InlinedFunctionBlock.Configuration(fb2);

		for(FunctionBlockInstance.CallSite i : fb1.ir.callSites.values())
			callSiteNodes.add(i.csNode);

		for(GraphNode<FunctionBlockInstance.CallSite> i :
				GraphNode.orderNodes(callSiteNodes)) {

			final FunctionBlockInstanceLink instLink =
					i.element.instance.getLink();

			// Skip instances without link as there is no chance that they can
			// be abstracted
			if(i.element.instance.getLink() == null) continue;

			Logging.log("Checking equal activation of [" +
					instLink.fbi1.name + "," + instLink.fbi2.name + "]");
			Logging.pushIndent();

			final boolean equalActivation = _checkEqualActivation(
					instLink, config1, config2,
					instLink.fbLink.varMappingIn.prefixed(instLink),
					smvVerifier);

			Logging.log((equalActivation ? "Equal" : "No equal") +
					" activation");

			// When function block instances are not activated equally, previous
			// results cannot be reused
			if(!equalActivation) continue;

			// Adapt the configurations depending on the equivalence of the
			// tested instances
			if(instLink.fbLink.isEquivalent()) {
				Logging.log("Abstract all call sites");
				config1.changeToAbstracted(instLink.fbi1);
				config2.changeToAbstracted(instLink.fbi2);
			} else {
				Logging.log("Use abstracted inlining at call sites");
				config1.changeToInlinedAbstract(instLink.fbi1);
				config2.changeToInlinedAbstract(instLink.fbi2);
			}
			Logging.popIndent();
		}

		final boolean fbEquivalent = _checkEquivalence(
				fb1.inlinedAbstracted, fb2.inlinedAbstracted,
				config1, config2, varMappingOut, smvVerifier);

		Logging.log(fbEquivalent ? "Equivalent" : "Not equivalent");
		Logging.popIndent();

		_state = fbEquivalent ? State.EQUIVALENT : State.NOT_EQUIVALENT;
	}

	public final void checkEquivalenceInlined(
			final SmvVerifier smvVerifier) {

		Logging.log("Checking equivalence (fully inlined) of [" +
				fb1.name + "," + fb2.name + "]");
		Logging.pushIndent();

		final boolean fbEquivalent = _checkEquivalence(
				fb1.inlinedAll, fb2.inlinedAll, varMappingOut, smvVerifier,
				"equiv_inlined_[" + fb1.name + "]-[" + fb2.name + "]");

		Logging.log(fbEquivalent ? "Equivalent" : "Not equivalent");
		Logging.popIndent();
	}

	public final void findInstanceLinks() {

		// necessary condition: the types of linked instances must also be
		// linked

		final Set<FunctionBlockLink> fbLinks1 = new HashSet<>();
		final Set<FunctionBlockLink> fbLinks2 = new HashSet<>();

		for(FunctionBlock i : fb1.cgNode.succElements)
			if(i.getLink() != null) fbLinks1.add(i.getLink());
		for(FunctionBlock i : fb2.cgNode.succElements)
			if(i.getLink() != null) fbLinks2.add(i.getLink());

		// Contains only instances whose type is used in both function blocks
		fbLinks1.retainAll(fbLinks2);

		// Holds a set for each function block of a link where the names of all
		// instances with this type are stored
		final Map<FunctionBlockLink, Pair<Set<String>>> groupedInstances =
				new HashMap<>();

		// Initialize 'groupedInstances'
		for(FunctionBlockLink i : fbLinks1)
			groupedInstances.put(
					i, new Pair<>(new HashSet<>(), new HashSet<>()));

		_groupInstances(fb1.fbInstances.values(), groupedInstances, Pair::getA);
		_groupInstances(fb2.fbInstances.values(), groupedInstances, Pair::getB);

		// Name matching
		for(Pair<Set<String>> i : groupedInstances.values())
			for(String j : i.a)
				// Only consider instances with equal names in both function
				// blocks
				if(i.b.contains(j)) _createInstanceLink(j, j, i.a, i.b);

		// Match instances where there is only one instance for each of the
		// linked function blocks
		for(Pair<Set<String>> i : groupedInstances.values())
			if(i.a.size() == 1 && i.b.size() == 1)
				_createInstanceLink(
						i.a.iterator().next(), i.b.iterator().next(), i.a, i.b);
	}

	public final Set<String> getCommonVariables(
			final FunctionBlock fb,
			final boolean       useInputMapping) {

		assert fb == fb1 || fb == fb2;

		final VariableMapping varMapping =
				useInputMapping ? varMappingIn : varMappingOut;

		if(fb == fb1) return varMapping.var2ByVar1.keySet();
		if(fb == fb2) return varMapping.var1ByVar2.keySet();
		return null;
	}

	public final State getState() {
		return _state;
	}

	public final boolean isEquivalent() {
		return _state == State.EQUIVALENT;
	}
}
