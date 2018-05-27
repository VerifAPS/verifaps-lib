package edu.kit.iti.formal.automation.sfclang

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.st.util.AstVisitor

/**
 *
 * SFCLangPrinter class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class SFCLangPrinter : AstVisitor<Any>()/*
    private CodeWriter cw = new CodeWriter();
    private StructuredTextPrinter stPrinter;

    public SFCLangPrinter() {
        stPrinter = new StructuredTextPrinter();
        stPrinter.setCodeWriter(cw);
    }

    public static String print(SFCImplementation a) {
        SFCLangPrinter p = new SFCLangPrinter();
        a.visit(p);
        return p.cw.toString();
    }

    @Override
    public Object visit(SFCImplementation decl) {
        cw.keyword("sfc").append(" ").append(decl.getName()).nl()
                .increaseIndent();

        stPrinter.visit(decl.getScope());

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
        cw.nl().keyword("action").append(" ").append(fbd.getName());
        cw.increaseIndent();
        cw.nl();
        stPrinter.visit(fbd.getScope());
        stPrinter.visit(fbd.getStBody());
        cw.decreaseIndent();
        cw.nl().keyword("end_action");
    }

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

    @Override
    public Object visit(TransitionDeclaration decl) {
        cw.nl().keyword("goto").append(" ");
        decl.getGuard().accept(stPrinter);
        cw.append(" ").keyword("::").append(" ");

        printList(decl.getFrom());
        cw.append(" ").append("->").append(" ");
        printList(decl.getTo());

        return null;
    }

    public CodeWriter getCodeWriter() {
        return cw;
    }
    public void setCodeWriter(CodeWriter cw) {
        this.cw = cw;
    }
*/
