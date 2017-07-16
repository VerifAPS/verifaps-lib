package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * <p>TransitionDeclaration class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TransitionDeclaration {
	Expression guard;
	Set<String> from = new HashSet<>();
	Set<String> to = new HashSet<>();

	/**
	 * <p>Getter for the field <code>guard</code>.</p>
	 *
	 * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
	 */
	public Expression getGuard() {
		return guard;
	}

	/**
	 * <p>Setter for the field <code>guard</code>.</p>
	 *
	 * @param guard a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
	 */
	public void setGuard(Expression guard) {
		this.guard = guard;
	}

	/**
	 * <p>Getter for the field <code>from</code>.</p>
	 *
	 * @return a {@link java.util.Set} object.
	 */
	public Set<String> getFrom() {
		return from;
	}

	/**
	 * <p>Setter for the field <code>from</code>.</p>
	 *
	 * @param from a {@link java.util.Set} object.
	 */
	public void setFrom(Set<String> from) {
		this.from = from;
	}

	/**
	 * <p>Getter for the field <code>to</code>.</p>
	 *
	 * @return a {@link java.util.Set} object.
	 */
	public Set<String> getTo() {
		return to;
	}

	/**
	 * <p>Setter for the field <code>to</code>.</p>
	 *
	 * @param to a {@link java.util.Set} object.
	 */
	public void setTo(Set<String> to) {
		this.to = to;
	}

	/**
	 * <p>accept.</p>
	 *
	 * @param v a {@link edu.kit.iti.formal.automation.sfclang.SFCAstVisitor} object.
	 * @param <T> a T object.
	 * @return a T object.
	 */
	public <T> T visit(SFCAstVisitor<T> v) {
		return v.visit(this);
	}

	/**
	 * <p>Setter for the field <code>from</code>.</p>
	 *
	 * @param ast a {@link java.util.List} object.
	 */
	public void setFrom(List<String> ast) {
		setFrom(new HashSet<>(ast));
	}

	/**
	 * <p>Setter for the field <code>to</code>.</p>
	 *
	 * @param ast a {@link java.util.List} object.
	 */
	public void setTo(List<String> ast) {
		setTo(new HashSet<>(ast));
	}
}
