package edu.kit.iti.formal.automation.st0;

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.st.visitors.Visitable;

import java.math.BigInteger;

/**
 * Created by weigl on 23/09/14.
 */
public class CalculateExponentialBlowOff extends DefaultVisitor<BigInteger> {
    public static BigInteger calc(Visitable visitable) {
        return visitable.visit(new CalculateExponentialBlowOff());
    }

    @Override
    public BigInteger defaultVisit(Visitable visitable) {
        return BigInteger.ONE;
    }

    @Override
    public BigInteger visit(CaseStatement caseStatement) {
        BigInteger i = BigInteger.ZERO;

        for (CaseStatement.Case aCase : caseStatement.getCases()) {
            i = i.add(aCase.getStatements().visit(this));
        }
        i = i.add(caseStatement.getElseCase().visit(this));
        return i;
    }


    @Override
    public BigInteger visit(IfStatement ifStatement) {
        BigInteger i = BigInteger.ZERO;

        for (GuardedStatement aCase : ifStatement.getConditionalBranches()) {
            i = i.add(aCase.getStatements().visit(this));
        }
        i = i.add(ifStatement.getElseBranch().visit(this));
        return i;
    }

    @Override
    public BigInteger visit(StatementList statements) {
        BigInteger i = BigInteger.ONE;
        for (Statement statement : statements) {
            i = i.multiply(statement.visit(this));
        }
        return i;
    }

    @Override
    public BigInteger visit(ProgramDeclaration programDeclaration) {
        return programDeclaration.getProgramBody().visit(this);
    }
}
