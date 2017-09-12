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

import edu.kit.iti.formal.automation.st.ast.Expression;

import java.util.Stack;

public final class PathCondition {

	public static final class Condition {

		public final int     condIndex;
		public final boolean isElse;

		private Condition(
				final int     condIndex,
				final boolean isElse) {

			this.condIndex = condIndex;
			this.isElse    = isElse;
		}
	}

	public final Stack<Condition> conditions = new Stack<>();

	public final PathCondition createSnapshot() {

		final PathCondition pathCondition = new PathCondition();
		for(Condition i : conditions)
			pathCondition.conditions.push(new Condition(i.condIndex, i.isElse));

		return pathCondition;
	}

	public final void pop() {
		conditions.pop();
	}

	public final void push(final int index) {
		conditions.push(new Condition(index, false));
	}

	public final void switchToElseBranch() {
		conditions.push(new Condition(conditions.pop().condIndex, true));
	}
}
