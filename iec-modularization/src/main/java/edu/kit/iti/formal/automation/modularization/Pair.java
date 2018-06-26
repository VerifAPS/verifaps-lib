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

public final class Pair<T> {

	public interface Selector<T> {
		T getElement(Pair<T> pair);
	}

	public T a;
	public T b;

	public Pair() {
		this(null, null);
	}

	public Pair(final T a, final T b) {
		this.a = a;
		this.b = b;
	}

	public static <T> T getA(final Pair<T> pair) {
		return pair.a;
	}

	public static <T> T getB(final Pair<T> pair) {
		return pair.b;
	}
}
