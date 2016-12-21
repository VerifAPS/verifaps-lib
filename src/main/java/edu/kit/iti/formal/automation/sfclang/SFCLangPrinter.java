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
import edu.kit.iti.formal.automation.st.util.CodeWriter;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * <p>SFCLangPrinter class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SFCLangPrinter implements SFCAstVisitor<Object> {
    private CodeWriter cw = new CodeWriter();
    private StructuredTextPrinter stPrinter;

    /**
     * <p>Constructor for SFCLangPrinter.</p>
     */
    public SFCLangPrinter() {
        stPrinter = new StructuredTextPrinter();
        stPrinter.setCodeWriter(cw);
    }

    /**
     * <p>print.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration} object.
     * @return a {@link java.lang.String} object.
     */
    public static String print(SFCDeclaration a) {
        SFCLangPrinter p = new SFCLangPrinter();
        a.visit(p);
        return p.cw.toString();
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(SFCDeclaration decl) {
        cw.keyword("sfc").append(" ").append(decl.getBlockName()).nl().increaseIndent();

        stPrinter.visit(decl.getLocalScope());

        cw.nl().nl();

        for (FunctionBlockDeclaration fbd : decl.getActions()) {
            printAction(fbd);
        }

        for (TransitionDeclaration t : decl.getTransitions()) {
            t.visit(this);
        }

        for (StepDeclaration s : decl.getSteps()) {
            s.visit(this);
        }

        cw.decreaseIndent().nl().keyword("end_sfc");
        return null;
    }

    private void printAction(FunctionBlockDeclaration fbd) {
        cw.nl().keyword("action").append(" ").append(fbd.getBlockName());
        cw.increaseIndent();
        cw.nl();
        stPrinter.visit(fbd.getLocalScope());
        stPrinter.visit(fbd.getFunctionBody());
        cw.decreaseIndent();
        cw.nl().keyword("end_action");
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(StepDeclaration decl) {
        cw.nl().keyword("step").append(" ").append(decl.getName());
        cw.increaseIndent();

        for (Map.Entry<String, List<String>> entry :
                decl.getEvents().entrySet()) {
            //FIXME
            for (String actionName : entry.getValue())
                cw.nl().keyword("on").append(" ").append(entry.getKey()).append(" ").append(actionName);
        }

        cw.decreaseIndent();
        cw.nl().keyword("end_step");

        return null;
    }

    private void appendEvents(List<String> seq, String type) {
        if (!seq.isEmpty()) {
            cw.nl().keyword("on").append(" ").keyword(type).append(" ");
            printList(seq);
            cw.nl();
        }
    }

    private void printList(List<String> seq) {
        for (String n : seq) {
            cw.append(n).append(", ");
        }
        cw.deleteLast(2);
    }

    private void printList(Set<String> seq) {
        ArrayList<String> array = new ArrayList<>(seq);
        array.sort(String.CASE_INSENSITIVE_ORDER);
        printList(array);
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(TransitionDeclaration decl) {
        cw.nl().keyword("goto").append(" ");
        decl.getGuard().visit(stPrinter);
        cw.append(" ").keyword("::").append(" ");

        printList(decl.getFrom());
        cw.append(" ").append("->").append(" ");
        printList(decl.getTo());

        return null;
    }

    /**
     * <p>getCodeWriter.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter getCodeWriter() {
        return cw;
    }

    /**
     * <p>setCodeWriter.</p>
     *
     * @param cw a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public void setCodeWriter(CodeWriter cw) {
        this.cw = cw;
    }

}
