package edu.kit.iti.formal.automation.st0;

import edu.kit.iti.formal.automation.st.ast.Literal;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.ast.TopLevelScopeElement;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st0.trans.ST0Transformation;
import lombok.RequiredArgsConstructor;

public class ConstantEmbedder implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        state.functions.values().parallelStream().forEach(this::process);
        process(state.theProgram);
    }

    private void process(TopLevelScopeElement topLevelScopeElement) {
        topLevelScopeElement.getLocalScope().stream()
                .forEach(variableDeclaration -> {
                    if (variableDeclaration.isConstant() && variableDeclaration.getInit() != null) {
                        assert variableDeclaration.getInit() instanceof Literal;
                        topLevelScopeElement.accept(
                                new ReplaceConstantVisitor(variableDeclaration.getName(),
                                        (Literal) variableDeclaration.getInit()));
                    }
                });
    }

    @RequiredArgsConstructor
    private class ReplaceConstantVisitor extends AstMutableVisitor {
        private final String constantName;
        private final Literal constant;

        @Override
        public Object visit(SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(constantName)) {
                assert !symbolicReference.hasSub();
                return constant;
            }
            return super.visit(symbolicReference);
        }
    }
}
