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

import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation;
import edu.kit.iti.formal.automation.sfclang.ast.SFCNetwork;
import edu.kit.iti.formal.automation.sfclang.ast.SFCStep;
import edu.kit.iti.formal.automation.sfclang.ast.SFCTransition;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st.util.CodeWriter;

/**
 * <p>DotPrinter class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DotPrinter extends AstVisitor<Void> {
    private CodeWriter cw = new CodeWriter();

    public static String dot(SFCImplementation decl) {
        DotPrinter p = new DotPrinter();
        p.visit(decl);
        return p.cw.toString();
    }

    @Override
    public Void visit(SFCImplementation decl) {
        cw.append("digraph g {").increaseIndent();
        cw.nl();
        decl.getNetworks().forEach(n -> visit(n));
        cw.decreaseIndent();
        cw.nl().append("}");
        return null;
    }

    public Void visit(SFCNetwork n) {
        cw.append("digraph f {").increaseIndent();
        cw.nl();
        n.getSteps().forEach(s -> s.accept(this));
        cw.decreaseIndent();
        cw.nl().append("}");
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Void visit(SFCStep decl) {
        cw.nl().append(decl.getName());
        cw.append(" [label=\"" + decl.getName() + "\", shape=rectangle]");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Void visit(SFCTransition decl) {
        for (SFCStep from : decl.getFrom()) {
            for (SFCStep to : decl.getTo())
                cw.nl().append(from).append(" -> ").append(to).append(";");
        }
        return null;
    }

}
