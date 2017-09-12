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
import edu.kit.iti.formal.automation.modularization.Util;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.HashSet;
import java.util.ListIterator;
import java.util.Set;

public final class DirectAssignment extends Assignment {

	private static final class DependencyCollector extends AstVisitor<Object> {

		private final Set<String> _depVariables = new HashSet<>();

		@Override
		public final Object visit(final SymbolicReference symbRef) {
			_depVariables.add(Util.referenceToString(symbRef, "."));
			return null;
		}
	}

	public final Expression expression;

	public DirectAssignment(
			final FunctionBlock owner,
			final Variable      variable,
			final Expression    expression) {

		super(owner, variable);
		this.expression = expression;
	}

	@Override
	public final void computeDependencies() {

		final DependencyCollector collector = new DependencyCollector();
		expression.accept(collector);

		for(Assignment i : _getDependencySet(collector._depVariables))
			_addDependency(i.variable, i.index);
	}

	@Override
	public final String toString() {

		if(expression != null) {

			final StructuredTextPrinter stPrinter = new StructuredTextPrinter();
			expression.accept(stPrinter);

			return variable.toString(index) + " := " + stPrinter.getString();

		} else {
			return variable.toString(index) + " := INIT";
		}
	}
}
