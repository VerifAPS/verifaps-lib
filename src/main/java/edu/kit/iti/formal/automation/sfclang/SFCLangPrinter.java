package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.util.CodeWriter;
import edu.kit.iti.formal.automation.visitors.StructuredTextPrinter;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

public class SFCLangPrinter implements SFCAstVisitor<Object> {
	private CodeWriter cw = new CodeWriter();
	private StructuredTextPrinter stPrinter;

	public SFCLangPrinter() {
		stPrinter = new StructuredTextPrinter();
		stPrinter.setCodeWriter(cw);
	}

	public static String print(SFCDeclaration a) {
		SFCLangPrinter p = new SFCLangPrinter();
		a.visit(p);
		return p.cw.toString();
	}

	@Override
	public Object visit(SFCDeclaration decl) {
		cw.keyword("sfc").append(" ").append(decl.getName()).nl().increaseIndent();

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
		cw.nl().keyword("action").append(" ").append(fbd.getBlockName());
		cw.increaseIndent();
		cw.nl();
		stPrinter.visit(fbd.getScope());
		stPrinter.visit(fbd.getFunctionBody());		
		cw.decreaseIndent();
		cw.nl().keyword("end_action");
	}

	@Override
	public Object visit(StepDeclaration decl) {
		cw.nl().keyword("step").append(" ").append(decl.getName());
		cw.increaseIndent();

		appendEvents(decl.getOnEntry(), "entry");
		appendEvents(decl.getOnActive(), "active");
		appendEvents(decl.getOnExit(), "exit");

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
		decl.getGuard().visit(stPrinter);
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

}
