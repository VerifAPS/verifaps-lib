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
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.LinkedList;
import java.util.List;

public class Variable {

	public static final String CONDITION_NAME = "$C";

	public final String                name;
	public final VariableDeclaration   declaration;
	public final List<Assignment>      assignments = new LinkedList<>();

	protected Variable(
			final FunctionBlock       owner,
			final VariableDeclaration declaration,
			final String              name) {

		this.declaration = declaration;
		this.name        = name;

		owner.addSsaVariable(this);
	}

	public Variable(
			final FunctionBlock       owner,
			final VariableDeclaration declaration) {

		this(
				owner,
				declaration,
				declaration != null ? declaration.getName() : CONDITION_NAME);
	}

	public final int getLatestIndex() {
		return assignments.size() - 1;
	}

	public final int getNextIndex() {
		return assignments.size();
	}

	public final String toString(final int index) {
		return name + '{' + index + '}';
	}
}
