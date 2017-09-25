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

import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class VariableMapping {

	public final Map<String, String> var2ByVar1 = new HashMap<>();
	public final Map<String, String> var1ByVar2 = new HashMap<>();

	public final Set<String> unmapped1 = new HashSet<>();
	public final Set<String> unmapped2 = new HashSet<>();

	public final boolean fullMatch;
	public final float   matchFactor;

	private void _addMatch(
			final String                           varName1,
			final String                           varName2,
			final Map<String, VariableDeclaration> remaining1,
			final Map<String, VariableDeclaration> remaining2) {

		var2ByVar1.put(varName1, varName2);
		var1ByVar2.put(varName2, varName1);

		remaining1.remove(varName1);
		remaining2.remove(varName2);
	}

	private VariableMapping(
			final VariableMapping source,
			final String          prefix1,
			final String          prefix2) {

		fullMatch   = source.fullMatch;
		matchFactor = source.matchFactor;

		for(Map.Entry<String, String> i : source.var2ByVar1.entrySet()) {

			final String newName1 = prefix1 + i.getKey();
			final String newName2 = prefix2 + i.getValue();

			var2ByVar1.put(newName1, newName2);
			var1ByVar2.put(newName2, newName1);
		}
	}

	public VariableMapping(
			final Map<String, VariableDeclaration> variables1,
			final Map<String, VariableDeclaration> variables2) {

		final Map<String, VariableDeclaration> varByName1 = new HashMap<>(variables1);
		final Map<String, VariableDeclaration> varByName2 = new HashMap<>(variables2);

		final Set<String> nameMatch = new HashSet<>();
		nameMatch.addAll   (varByName1.keySet());
		nameMatch.retainAll(varByName2.keySet());

		for(String i : nameMatch) {

			final VariableDeclaration var1 = varByName1.get(i);
			final VariableDeclaration var2 = varByName2.get(i);

			if(var1.getDataType().equals(var2.getDataType()))
				_addMatch(i, i, varByName1, varByName2);
		}

		// TODO: match by datatype

		unmapped1.addAll(varByName1.keySet());
		unmapped2.addAll(varByName2.keySet());

		fullMatch   = unmapped1.isEmpty() && unmapped2.isEmpty();
		matchFactor =
				2 * var2ByVar1.size() / (variables1.size() + variables2.size());
	}

	public final VariableMapping prefixed(
			final FunctionBlockInstanceLink fbiLink) {

		return new VariableMapping(
				this,
				fbiLink.fbi1.name + "$",
				fbiLink.fbi2.name + "$");
	}
}
