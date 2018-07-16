package edu.kit.iti.formal.automation.st0.trans

import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.trans.CodeTransformation
/*
class ConstantEmbedding : CodeTransformation {
    override fun transform(state: TransformationState): TransformationState {
        state.scope
                .forEach {
                    if (it.isConstant && it.init != null) {
                        assert(it.init is Literal)
                        topLevelScopeElement.accept(
                                ReplaceConstantVisitor(it.name, it.init as Literal))
                    }
                }

        return state
    }

    private inner class ReplaceConstantVisitor(private val constantName: String,
                                               private val constant: Literal) : AstMutableVisitor() {

        override fun visit(symbolicReference: SymbolicReference): Expression {
            if (symbolicReference.identifier == constantName) {
                assert(!symbolicReference.hasSub())
                return constant
            }
            return super.visit(symbolicReference)
        }
    }
}
*/