package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 03/10/14.
 */
public class ExpressionReplacer extends AstCopyVisitor {
    private StatementList statements;
    private Map<Expression, Expression> replacements = new HashMap<>();

    public StatementList getStatements() {
        return statements;
    }

    public void setStatements(StatementList statements) {
        this.statements = statements;
    }

    public Map<Expression, Expression> getReplacements() {
        return replacements;
    }

    public void setReplacements(Map<Expression, Expression> replacements) {
        this.replacements = replacements;
    }


    @Override
    public Object visit(SymbolicReference symbolicReference) {
        if (replacements.containsKey(symbolicReference)) {
            return replacements.get(symbolicReference);
        }
        return super.visit(symbolicReference);
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        if (replacements.containsKey(unaryExpression)) {
            return replacements.get(unaryExpression);
        }
        return super.visit(unaryExpression);
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        if (replacements.containsKey(binaryExpression)) {
            return replacements.get(binaryExpression);
        }
        return super.visit(binaryExpression);
    }

    public Collection<? extends Statement> replace() {
        return (StatementList) getStatements().visit(this);
    }
}
