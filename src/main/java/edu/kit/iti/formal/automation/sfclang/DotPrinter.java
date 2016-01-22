package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.util.CodeWriter;

public class DotPrinter implements SFCAstVisitor<CodeWriter> {

	private CodeWriter cw = new CodeWriter();

	public static String dot(SFCDeclaration decl) {
		DotPrinter p = new DotPrinter();
		p.visit(decl);
		return p.cw.toString();
	}

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

	@Override
	public CodeWriter visit(StepDeclaration decl) {
		cw.nl().append(decl.getName());
		return cw.append(" [label=\"" + decl.getName() + "\", shape=rectangle]");
	}

	@Override
	public CodeWriter visit(TransitionDeclaration decl) {
		for (String from : decl.getFrom()) {
			for (String to : decl.getTo())
				cw.nl().append(from).append(" -> ").append(to).append(";");
		}
		return cw;
	}

}
