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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

public final class FunctionBlockInstanceLink {

	public final FunctionBlockInstance fbi1;
	public final FunctionBlockInstance fbi2;
	public final FunctionBlockLink     fbLink;

	public FunctionBlockInstanceLink(
			final FunctionBlockInstance fbi1,
			final FunctionBlockInstance fbi2) {

		this.fbi1   = fbi1;
		this.fbi2   = fbi2;
		this.fbLink = fbi1.type.getLink();

		// The types of the instances must be linked as well
		assert fbLink != null && fbLink == fbi2.type.getLink();

		// We want the instances to have the same number of call sites
		assert fbi1.callSites.size() == fbi2.callSites.size();

		fbi1.setLink(this);
		fbi2.setLink(this);

		// TODO: The call site links are not created intelligently
		for(int i = 0; i < fbi1.callSites.size(); i++)
			new CallSiteLink(fbi1.callSites.get(i), fbi2.callSites.get(i));
	}
}
