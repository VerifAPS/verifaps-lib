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

import edu.kit.iti.formal.automation.st.ast.TypeDeclaration;

public final class AbstractionVariable {

	public interface NameSelector {
		String getName(AbstractionVariable var);
	}

	public final InlinedFunctionBlock fb1;
	public final InlinedFunctionBlock fb2;

	public final String name1;
	public final String name2;

	public final TypeDeclaration type;

	public AbstractionVariable(
			final InlinedFunctionBlock fb1,
			final InlinedFunctionBlock fb2,
			final String               name1,
			final String               name2,
			final TypeDeclaration      type) {

		this.fb1   = fb1;
		this.fb2   = fb2;
		this.name1 = name1;
		this.name2 = name2;
		this.type  = type;

		if(fb1 != null) fb1.abstractionVars.put(name1, this);
		if(fb2 != null) fb2.abstractionVars.put(name2, this);
	}

	public AbstractionVariable(
			final InlinedFunctionBlock fb1,
			final InlinedFunctionBlock fb2,
			final String               instName1,
			final String               instName2,
			final AbstractionVariable  inlinedVar) {

		this(
				fb1, fb2,
				fb1 != null ? instName1 + "$" + inlinedVar.name1 : null,
				fb2 != null ? instName2 + "$" + inlinedVar.name2 : null,
				inlinedVar.type);
	}

	public static String getName1(final AbstractionVariable var) {
		return var.name1;
	}

	public static String getName2(final AbstractionVariable var) {
		return var.name2;
	}

	public final boolean isCommon() {
		return fb1 != null && fb2 != null;
	}
}
