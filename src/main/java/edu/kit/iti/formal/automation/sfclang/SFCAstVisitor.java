package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;

public interface SFCAstVisitor<T> {
	public T visit(SFCDeclaration decl);
	public T visit(StepDeclaration decl);
	public T visit(TransitionDeclaration decl);
}
