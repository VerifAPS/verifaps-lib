package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.ast.*;
import org.sosy_lab.java_smt.api.*;

/**
 * Created by weigl on 20.12.16.
 */
public class SMTPrinter implements SMVAstVisitor<Formula> {
    private final int cc;
    private final BitvectorFormulaManager bitmgr;
    private final BooleanFormulaManager boolmgr;
    private final SMTVariableFactory vfactory;
    private final FormulaManager fmgr;

    public SMTPrinter(FormulaManager fmgr, SMTVariableFactory factory, int currentTimeFrame) {
        cc = currentTimeFrame;
        vfactory = factory;
        this.fmgr = fmgr;
        boolmgr = fmgr.getBooleanFormulaManager();
        bitmgr = fmgr.getBitvectorFormulaManager();
    }

    @Override
    public Formula visit(SMVAst top) {
        return null;
    }

    @Override
    public Formula visit(SVariable v) {
        if (v.getName().indexOf('_') >= 0) {
            String n = v.getName().substring(0, v.getName().indexOf('_'));
            int c = Integer.parseInt(v.getName().substring(
                    v.getName().lastIndexOf('$') + 1));
            return vfactory.getVariable(n, v.getSMVType(), cc - c);
        } else {
            return vfactory.getVariable(v.getName(), v.getSMVType());
        }
    }

    @Override
    public Formula visit(SBinaryExpression be) {
        Formula l = be.left.accept(this);
        Formula r = be.right.accept(this);

        switch (be.operator) {
            case AND:
                return boolmgr.and((BooleanFormula) l, (BooleanFormula) r);
            case OR:
                return boolmgr.and((BooleanFormula) l, (BooleanFormula) r);
            case IMPL:
                return boolmgr.implication((BooleanFormula) l, (BooleanFormula) r);
            case NOT_EQUAL:
                return bitmgr.and((BitvectorFormula) l, (BitvectorFormula) r);
            case EQUAL:
                return bitmgr.and((BitvectorFormula) l, (BitvectorFormula) r);
            case PLUS:
                return bitmgr.add((BitvectorFormula) l, (BitvectorFormula) r);
            case MINUS:
                return bitmgr.subtract((BitvectorFormula) l, (BitvectorFormula) r);
            case GREATER_EQUAL:
                return bitmgr.greaterOrEquals((BitvectorFormula) l, (BitvectorFormula) r, true);
            case GREATER_THAN:
                return bitmgr.greaterThan((BitvectorFormula) l, (BitvectorFormula) r, true);
            case LESS_EQUAL:
                return bitmgr.lessOrEquals((BitvectorFormula) l, (BitvectorFormula) r, true);
            case LESS_THAN:
                return bitmgr.lessThan((BitvectorFormula) l, (BitvectorFormula) r, true);
            case DIV:
                return bitmgr.divide((BitvectorFormula) l, (BitvectorFormula) r, true);
            case MOD:
                return bitmgr.modulo((BitvectorFormula) l, (BitvectorFormula) r, true);
        }
        throw new IllegalStateException("operator: " + be.operator + " not covered");
    }

    @Override
    public Formula visit(SUnaryExpression ue) {
        return fmgr.parse(
                String.format("(%s %s)", ue.operator.symbol(), ue.expr.accept(this)));
    }

    @Override
    public Formula visit(SLiteral l) {
        if (l.getSMVType() == SMVType.BOOLEAN)
            return boolmgr.makeBoolean(Boolean.valueOf(l.value.toString()));

        SMVType.SMVTypeWithWidth wtype = (SMVType.SMVTypeWithWidth) l.getSMVType();
        return bitmgr.makeBitvector(wtype.getWidth(), (Long) l.value);
    }

    @Override
    public Formula visit(SAssignment a) {
        return null;
    }

    @Override
    public Formula visit(SCaseExpression ce) {
        //return visit(ce.cases, 0);
        return null;
    }

    /*private String visit(List<SCaseExpression.Case> cases, int pos) {
        if (pos + 1 == cases.size())
            return cases.get(pos).then.accept(this);

        return String.format("(ite %s %s %s)",
                cases.get(pos).condition.accept(this),
                cases.get(pos).then.accept(this),
                visit(cases, pos + 1));
    }*/

    @Override
    public Formula visit(SMVModule smvModule) {
        return null;
    }

    @Override
    public Formula visit(SFunction func) {
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
