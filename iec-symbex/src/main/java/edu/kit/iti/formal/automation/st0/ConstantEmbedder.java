package edu.kit.iti.formal.automation.st0;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.Literal;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.ast.HasScope;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st0.trans.ST0Transformation;
import lombok.RequiredArgsConstructor;

public class ConstantEmbedder implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        state.functions.values().parallelStream().forEach(this::process);
        process(state.theProgram);
    }

    private void process(HasScope topLevelScopeElement) {
        topLevelScopeElement.getScope().stream()
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
