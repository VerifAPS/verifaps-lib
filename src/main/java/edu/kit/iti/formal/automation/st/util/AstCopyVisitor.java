package edu.kit.iti.formal.automation.st.util;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.ArrayList;
import java.util.List;

/**
 * @author weigla
 * @date 26.06.2014
 * <p>
 * <bold>ATTTENTION</bold> this is only useable on statement level and below!
 * <p>
 * This visitors defines all function with go down and setting the results of visit as the new value.
 */
public class AstCopyVisitor extends DefaultVisitor<Object> {
    @Override
    public Object defaultVisit(Visitable visitable) {
        System.out.println("AstTransform.defaultVisit");
        System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return visitable;
    }

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        AssignmentStatement statement = new AssignmentStatement(
                (Reference) assignmentStatement.getLocation().visit(this),
                (Expression) assignmentStatement.getExpression().visit(this)
        );
        setPositions(assignmentStatement, statement);
        return statement;
    }

    @Override
    public Object visit(CaseConditions.IntegerCondition integerCondition) {
        return integerCondition;
    }

    @Override
    public Object visit(CaseConditions.Enumeration enumeration) {
        return enumeration;
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        BinaryExpression be = new BinaryExpression(
                (Expression) binaryExpression.getLeftExpr().visit(this),
                (Expression) binaryExpression.getRightExpr().visit(this),
                binaryExpression.getOperator());
        return be;
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        UnaryExpression ue = new UnaryExpression(unaryExpression.getOperator(), (Expression) unaryExpression.getExpression().visit(this));
        return ue;
    }

    @Override
    public Object visit(RepeatStatement repeatStatement) {
        RepeatStatement w = new RepeatStatement();
        w.setCondition((Expression) repeatStatement.getCondition().visit(this));
        w.setStatements((StatementList) repeatStatement.getStatements().visit(this));
        setPositions(repeatStatement, w);
        return w;
    }

    @Override
    public Object visit(WhileStatement whileStatement) {
        WhileStatement w = new WhileStatement();
        w.setCondition((Expression) whileStatement.getCondition().visit(this));
        w.setStatements((StatementList) whileStatement.getStatements().visit(this));
        setPositions(whileStatement, w);
        return w;
    }


    @Override
    public Object visit(CaseStatement caseStatement) {
        CaseStatement cs = new CaseStatement();

        for (CaseStatement.Case c : caseStatement.getCases()) {
            cs.addCase((CaseStatement.Case) c.visit(this));
        }

        cs.setExpression((Expression) caseStatement.getExpression().visit(this));
        cs.setElseCase((StatementList) caseStatement.getElseCase().visit(this));

        setPositions(caseStatement, cs);
        return cs;
    }

    /*@Override
    public Object visit(SymbolicReference symbolicReference) {
        SymbolicReference sr = new SymbolicReference(symbolicReference);

        if (symbolicReference.getSubscripts() != null) {
            sr.setSubscripts(new ExpressionList());
            for (Expression e : symbolicReference.getSubscripts()) {
                sr.getSubscripts().add((Expression) e.visit(this));
            }
        }

        if (sr.getSub() != null)
            sr.setSub((SymbolicReference) sr.getSub().visit(this));

        return sr;
    }
*/
    @Override
    public Object visit(StatementList statements) {
        StatementList r = new StatementList();
        for (Statement s : statements) {
            //       if(s != null)
            if (s == null) {
                System.out.println("statements = [" + statements + "]");
            }
            Object t = s.visit(this);
            if (t instanceof StatementList) {
                StatementList statementList = (StatementList) t;
                r.addAll(statementList);
            } else {
                r.add((Statement) t);
            }
        }
        return r;
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        ProgramDeclaration pd = new ProgramDeclaration(programDeclaration);
        pd.setScope((VariableScope) programDeclaration.getScope().visit(this));
        pd.setProgramBody((StatementList) programDeclaration.getProgramBody().visit(this));
        return pd;
    }

    @Override
    public Object visit(VariableScope variableScope) {
        VariableScope vs = new VariableScope();
        for (VariableDeclaration vd : variableScope.getVariableMap().values())
            vs.add((VariableDeclaration) vd.visit(this));
        return vs;
    }

    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        return new ScalarValue<>(tsScalarValue.getDataType(), tsScalarValue.getValue());
    }


    @Override
    public Object visit(FunctionCall functionCall) {
        FunctionCall fc = new FunctionCall(functionCall);

        fc.getParameters().clear();
        for (FunctionCall.Parameter p : functionCall.getParameters()) {
            fc.getParameters().add(new FunctionCall.Parameter(p.getName(), p.isOutput(), (Expression) p.getExpression().visit(this)));
        }
        return fc;
    }

    @Override
    public Object visit(ForStatement forStatement) {
        ForStatement f = new ForStatement();
        f.setVariable(forStatement.getVariable());
        f.setStart((Expression) forStatement.getStart().visit(this));
        f.setStatements((StatementList) forStatement.getStatements().visit(this));
        if (forStatement.getStep() != null)
            f.setStep((Expression) forStatement.getStep().visit(this));
        f.setStop((Expression) forStatement.getStop().visit(this));
        setPositions(forStatement, f);
        return f;
    }

    @Override
    public Object visit(IfStatement ifStatement) {
        IfStatement i = new IfStatement();
        for (GuardedStatement gc : ifStatement.getConditionalBranches()) {
            i.addGuardedCommand((GuardedStatement) gc.visit(this));
        }
        i.setElseBranch((StatementList) ifStatement.getElseBranch().visit(this));
        setPositions(ifStatement, i);
        return i;
    }

    private Top setPositions(Top old, Top fresh) {
        fresh.setStartPosition(old.getStartPosition());
        fresh.setEndPosition(old.getEndPosition());
        return fresh;
    }

    @Override
    public Object visit(CommentStatement commentStatement) {
        return commentStatement;
    }


    @Override
    public Object visit(GuardedStatement guardedStatement) {
        GuardedStatement gs = new GuardedStatement();
        gs.setCondition((Expression) guardedStatement.getCondition().visit(this));
        gs.setStatements((StatementList) guardedStatement.getStatements().visit(this));
        return setPositions(guardedStatement, gs);
    }

    @Override
    public Object visit(FunctionCallStatement functionCallStatement) {
        FunctionCallStatement fc = new FunctionCallStatement((FunctionCall) functionCallStatement.getFunctionCall().visit(this));
        return fc;
    }

    @Override
    public Object visit(CaseStatement.Case aCase) {
        CaseStatement.Case c = new CaseStatement.Case();

        List<CaseConditions> v = this.<CaseConditions>visitList(aCase.getConditions());
        c.setConditions(v);
        c.setStatements((StatementList) aCase.getStatements().visit(this));

        return setPositions(aCase, c);
    }

    private <T> List<T> visitList(List<? extends Visitable> list) {
        List l = new ArrayList();
        for (Visitable v : list)
            l.add((T) v.visit(this));
        return l;
    }


    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        VariableDeclaration vd = new VariableDeclaration();
        vd.setDataType(variableDeclaration.getDataType());
        vd.setDataTypeName(variableDeclaration.getDataTypeName());
        if (variableDeclaration.getInit() != null)
            vd.setInit((Initialization) variableDeclaration.getInit().visit(this));
        vd.setName(variableDeclaration.getName());
        vd.setType(variableDeclaration.getType());
        return vd;
    }

    @Override
    public Object visit(ReturnStatement returnStatement) {
        return setPositions(returnStatement, new ReturnStatement());
    }
}
