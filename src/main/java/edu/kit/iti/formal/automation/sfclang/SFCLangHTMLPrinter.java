package edu.kit.iti.formal.automation.sfclang;


import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.util.HTMLCodeWriter;
import edu.kit.iti.formal.automation.visitors.StructuredTextHtmlPrinter;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class SFCLangHTMLPrinter implements SFCAstVisitor<HTMLCodeWriter> {
	private HTMLCodeWriter hcw = new HTMLCodeWriter();
	private StructuredTextHtmlPrinter stPrinter;

	public SFCLangHTMLPrinter() {
		stPrinter = new StructuredTextHtmlPrinter();
		stPrinter.setCodeWriter(hcw);
	}

	public static String html(SFCDeclaration decl) {
		SFCLangHTMLPrinter p = new SFCLangHTMLPrinter();
		p.hcw.appendHtmlPreamble();
		p.visit(decl);
		return p.hcw.toString();
	}

	@Override
	public HTMLCodeWriter visit(SFCDeclaration decl) {

		hcw.keyword("sfc").append(" ").append(decl.getName()).nl().increaseIndent();

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
		decl.getGuard().visit(stPrinter);
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

		appendEvents(decl.getOnEntry(), "entry");
		appendEvents(decl.getOnActive(), "active");
		appendEvents(decl.getOnExit(), "exit");

		hcw.decreaseIndent();
		hcw.nl().keyword("end_step");

		return hcw;
	}

	private void printAction(FunctionBlockDeclaration fbd) {
		hcw.nl().keyword("action").append(" ").append(fbd.getBlockName());
		hcw.increaseIndent();
		hcw.nl();
		stPrinter.visit(fbd.getScope());
		stPrinter.visit(fbd.getFunctionBody());
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

}
