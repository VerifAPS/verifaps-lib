package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.ast.*;

import java.util.List;

/**
 * Created by weigl on 20.12.16.
 */
public class SMTPrinter implements SMVAstVisitor<String> {
    private final int cc;

    public SMTPrinter(int currentTimeFrame) {
        cc = currentTimeFrame;
    }

    @Override
    public String visit(SMVAst top) {
        return null;
    }

    @Override
    public String visit(SVariable v) {
        if (v.getName().indexOf('_') >= 0) {
            String n = v.getName().substring(0, v.getName().indexOf('_'));
            int c = Integer.parseInt(v.getName().substring(
                    v.getName().lastIndexOf('$') + 1));
            return SMTVariableFactory.getVariable(n, v.getSMVType(), cc - c);
        } else {
            return SMTVariableFactory.getVariable(v.getName(), v.getSMVType());
        }
    }

    @Override
    public String visit(SBinaryExpression be) {
        String l = be.left.accept(this);
        String r = be.right.accept(this);
        return String.format("(%s %s %s", getOperator(be.operator), l, r);
    }

    private String getOperator(SBinaryOperator operator) {
        switch (operator) {
            case AND:
                return "and";
            case OR:
                return "or";
            case IMPL:
                return "->";
            case NOT_EQUAL:
                return "!=";
            case EQUAL:
                return "=";
            case PLUS:
                return "bvadd";
            case MINUS:
                return "bvsub";
            case GREATER_EQUAL:
                return ">=";
            case GREATER_THAN:
                return ">";
            case LESS_EQUAL:
                return "<=";
            case LESS_THAN:
                return "<";
            case DIV:
                return "bvdiv";
            case MOD:
                return "bvmod";
        }
        return "";
    }

    @Override
    public String visit(SUnaryExpression ue) {
        return String.format("(%s %s)", ue.operator.symbol(),
                ue.expr.accept(this));
    }

    @Override
    public String visit(SLiteral l) {
        return l.value.toString();
    }

    @Override
    public String visit(SAssignment a) {
        return null;
    }

    @Override
    public String visit(SCaseExpression ce) {
        return visit(ce.cases, 0);
    }

    private String visit(List<SCaseExpression.Case> cases, int pos) {
        if (pos + 1 == cases.size())
            return cases.get(pos).then.accept(this);

        return String.format("(ite %s %s %s)",
                cases.get(pos).condition.accept(this),
                cases.get(pos).then.accept(this),
                visit(cases, pos + 1));
    }

    @Override
    public String visit(SMVModule smvModule) {
        return null;
    }

    @Override
    public String visit(SFunction func) {
        return null;
        /*
        return "(" + func.getFunctionName() + " " +
                Arrays.stream(func.getArguments())
                        .map(a -> a.accept(this))
                        .reduce((a, b) -> a + " " + b)
                        .orElse("")
                + ")";*/
    }
}
