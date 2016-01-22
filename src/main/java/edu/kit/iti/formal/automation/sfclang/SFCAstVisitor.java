package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;

public interface SFCAstVisitor<T> {
    T visit(SFCDeclaration decl);

    T visit(StepDeclaration decl);

    T visit(TransitionDeclaration decl);
}
