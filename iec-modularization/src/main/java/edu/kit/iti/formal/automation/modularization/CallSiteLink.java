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

public final class CallSiteLink {

	public final FunctionBlockInstance.CallSite cs1;
	public final FunctionBlockInstance.CallSite cs2;
	public final FunctionBlockInstanceLink      fbiLink;

	public CallSiteLink(
			final FunctionBlockInstance.CallSite cs1,
			final FunctionBlockInstance.CallSite cs2) {

		this.cs1     = cs1;
		this.cs2     = cs2;
		this.fbiLink = cs1.instance.getLink();

		// The instances of the call sites must be linked as well
		assert fbiLink != null && fbiLink == cs1.instance.getLink();

		cs1.setLink(this);
		cs2.setLink(this);
	}
}
