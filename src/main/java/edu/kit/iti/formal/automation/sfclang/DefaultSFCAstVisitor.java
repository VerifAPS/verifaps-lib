package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;

/**
 *
 */
public class DefaultSFCAstVisitor implements SFCAstVisitor<Object> {

	private SFCDeclaration current;

	@Override
	public Object visit(SFCDeclaration decl) {
		current = decl;

		for (TransitionDeclaration t : decl.getTransitions()) {
			t.visit(this);
		}
		
		for (StepDeclaration s : decl.getSteps()) {
			s.visit(this);
		}

		return decl;
	}

	@Override
	public Object visit(StepDeclaration decl) {
		return decl;
	}

	@Override
	public Object visit(TransitionDeclaration decl) {
		return decl;
	}

}
