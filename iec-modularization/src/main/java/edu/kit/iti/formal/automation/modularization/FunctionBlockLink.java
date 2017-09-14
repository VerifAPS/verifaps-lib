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

public class FunctionBlockLink {

	public final FunctionBlock fb1;
	public final FunctionBlock fb2;
	public final float         nameMatch;
	public final float         signatureMatch;

	public FunctionBlockLink(
			final FunctionBlock fb1,
			final FunctionBlock fb2) {

		this.fb1 = fb1;
		this.fb2 = fb2;
		this.nameMatch = 1;
		this.signatureMatch = 1;
	}
}
