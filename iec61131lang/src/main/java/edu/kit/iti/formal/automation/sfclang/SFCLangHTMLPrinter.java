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


import edu.kit.iti.formal.automation.st.StructuredTextHtmlPrinter;

/**
 * <p>SFCLangHTMLPrinter class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SFCLangHTMLPrinter extends StructuredTextHtmlPrinter {
 /*
    private HTMLCodeWriter hcw = new HTMLCodeWriter();
    private StructuredTextHtmlPrinter stPrinter;

    public SFCLangHTMLPrinter() {
        stPrinter = new StructuredTextHtmlPrinter();
        stPrinter.setCodeWriter(hcw);
    }

    public static String html(SFCImplementation decl) {
        SFCLangHTMLPrinter p = new SFCLangHTMLPrinter();
        p.hcw.appendHtmlPreamble();
        p.visit(decl);
        return p.hcw.toString();
    }

    @Override
    public HTMLCodeWriter visit(SFCImplementation decl) {

        hcw.keyword("sfc").append(" ").append(decl.getIdentifier()).nl()
                .increaseIndent();

        stPrinter.visit(decl.getScope());

        hcw.nl().nl();

        for (FunctionBlockDeclaration fbd : decl.getActions()) {
            printAction(fbd);
        }

        for (TransitionDeclaration t : decl.getTransitions()) {
            t.visit(this);
        }

        for (StepDeclaration s : decl.getSteps()) {
            s.visit(this);
        }

        hcw.decreaseIndent().nl().keyword("end_sfc");
        return hcw;
    }

    @Override
    public HTMLCodeWriter visit(TransitionDeclaration decl) {
        hcw.nl().keyword("goto").append(" ");
        decl.getGuard().accept(stPrinter);
        hcw.append(" ").keyword("::").append(" ");

        printList(decl.getFrom());
        hcw.append(" ").keyword("->").append(" ");
        printList(decl.getTo());

        return hcw;
    }

    @Override
    public HTMLCodeWriter visit(StepDeclaration decl) {
        hcw.nl().keyword("step").append(" ").append(decl.getName());
        hcw.increaseIndent();

		//FIXME
        appendEvents(decl.getOnEntry(), "entry");
		appendEvents(decl.getOnActive(), "active");
		appendEvents(decl.getOnExit(), "exit");

        hcw.decreaseIndent();
        hcw.nl().

    keyword("end_step");

        return hcw;
}

    private void printAction(FunctionBlockDeclaration fbd) {
        hcw.nl().keyword("action").append(" ").append(fbd.getIdentifier());
        hcw.increaseIndent();
        hcw.nl();
        stPrinter.visit(fbd.getScope());
        stPrinter.visit(fbd.getStBody());
        hcw.decreaseIndent();
        hcw.nl().keyword("end_action");
    }

    private void appendEvents(List<String> seq, String type) {
        if (!seq.isEmpty()) {
            hcw.nl().keyword("on").append(" ").keyword(type).append(" ");
            printList(seq);
            hcw.nl();
        }
    }

    private void printList(List<String> seq) {
        for (String n : seq) {
            hcw.append(n).append(", ");
        }
        hcw.deleteLast(2);
    }

    private void printList(Set<String> seq) {
        ArrayList<String> array = new ArrayList<>(seq);
        array.sort(String.CASE_INSENSITIVE_ORDER);
        printList(array);
    }

    public HTMLCodeWriter getCodeWriter() {
        return hcw;
    }

    public void setCodeWriter(HTMLCodeWriter cw) {
        this.hcw = cw;
    }
*/
}
