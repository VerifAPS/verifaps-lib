package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st.ast.BinaryExpression;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.UnaryExpression;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;

import java.util.Map;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class ExpressionEmbedder extends AstCopyVisitor {
    private final Map<Expression, Expression> assignments;

    public ExpressionEmbedder(Map<Expression, Expression> assignments) {
        this.assignments = assignments;
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        return super.visit(binaryExpression);
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        return super.visit(unaryExpression);
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        return copyOrSubstitute(symbolicReference);
    }

    private Expression copyOrSubstitute(Expression expression) {
        return assignments.getOrDefault(expression,
                //TODO infinite loop call
                (Expression) expression.visit(this));
    }
}
