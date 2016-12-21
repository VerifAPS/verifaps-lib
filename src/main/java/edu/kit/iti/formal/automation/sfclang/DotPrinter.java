package edu.kit.iti.formal.automation.sfclang;

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

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.st.util.CodeWriter;

/**
 * <p>DotPrinter class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DotPrinter implements SFCAstVisitor<CodeWriter> {

	private CodeWriter cw = new CodeWriter();

	/**
	 * <p>dot.</p>
	 *
	 * @param decl a {@link edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration} object.
	 * @return a {@link java.lang.String} object.
	 */
	public static String dot(SFCDeclaration decl) {
		DotPrinter p = new DotPrinter();
		p.visit(decl);
		return p.cw.toString();
	}

	/** {@inheritDoc} */
	@Override
	public CodeWriter visit(SFCDeclaration decl) {
		cw.append("digraph g {").increaseIndent();
		cw.nl();

		for (StepDeclaration step : decl.getSteps()) {
			step.visit(this);
		}

		cw.decreaseIndent();
		cw.nl().append("}");
		return cw;
	}

	/** {@inheritDoc} */
	@Override
	public CodeWriter visit(StepDeclaration decl) {
		cw.nl().append(decl.getName());
		return cw.append(" [label=\"" + decl.getName() + "\", shape=rectangle]");
	}

	/** {@inheritDoc} */
	@Override
	public CodeWriter visit(TransitionDeclaration decl) {
		for (String from : decl.getFrom()) {
			for (String to : decl.getTo())
				cw.nl().append(from).append(" -> ").append(to).append(";");
		}
		return cw;
	}

}
