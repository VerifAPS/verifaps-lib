package edu.kit.iti.formal.automation.st.util;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * @author weigla
 * @date 26.06.2014
 * This visitors defines all function with go down and setting the results of visit as the new value.
 * Not copying datastructures.
 */
public class AstMutableVisitor extends DefaultVisitor<Object> {
    @Override
    public Object defaultVisit(Visitable visitable) {
        System.out.println("AstTransform.defaultVisit");
        System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return visitable;
    }

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        assignmentStatement.setExpression((Expression) assignmentStatement.getExpression().visit(this));
        assignmentStatement.setLocation((Reference) assignmentStatement.getLocation().visit(this));
        return assignmentStatement;
    }

    @Override
    public Object visit(CaseConditions.IntegerCondition integerCondition) {
        ScalarValue sv = (ScalarValue) integerCondition.getValue().<Object>visit(this);
        integerCondition.setValue(sv);
        return integerCondition;
    }

    @Override
    public Object visit(CaseConditions.Enumeration enumeration) {
        enumeration.setStart((ScalarValue<EnumerateType, String>) enumeration.getStart().<Object>visit(this));
        enumeration.setStop((ScalarValue<EnumerateType, String>) enumeration.getStop().<Object>visit(this));
        return enumeration;
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        binaryExpression.setLeftExpr(
                (Expression) binaryExpression.getLeftExpr().<Object>visit(this));

        binaryExpression.setRightExpr(
                (Expression) binaryExpression.getRightExpr().<Object>visit(this));

        return binaryExpression;
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        unaryExpression.setExpression((Expression) unaryExpression.getExpression().<Object>visit(this));
        return unaryExpression;
    }

    @Override
    public Object visit(RepeatStatement repeatStatement) {
        repeatStatement.setCondition((Expression) repeatStatement.getCondition().<Object>visit(this));
        repeatStatement.setStatements((StatementList) repeatStatement.getStatements().<Object>visit(this));
        return repeatStatement;
    }

    @Override
    public Object visit(WhileStatement whileStatement) {
        whileStatement.setCondition((Expression) whileStatement.getCondition().<Object>visit(this));
        whileStatement.setStatements((StatementList) whileStatement.getStatements().<Object>visit(this));
        return whileStatement;
    }


    @Override
    public Object visit(CaseStatement caseStatement) {
        LinkedList<CaseStatement.Case> l = new LinkedList<>();
        for (CaseStatement.Case c : caseStatement.getCases()) {
            l.add((CaseStatement.Case) c.visit(this));
        }

        caseStatement.setCases(l);

        caseStatement.setExpression((Expression) caseStatement.getExpression().visit(this));
        caseStatement.setElseCase((StatementList) caseStatement.getElseCase().visit(this));
        return caseStatement;
    }


    /*
    @Override
    public Object visit(SymbolicReference symbolicReference) {

        if (symbolicReference.getSub() != null)
            symbolicReference.setSub((Reference) symbolicReference.getSub().<Object>visit(this));

        if (symbolicReference.getSubscripts() != null)
            symbolicReference.setSubscripts((ExpressionList)
                    symbolicReference.getSubscripts().<Object>visit(this));

        return symbolicReference;
    }*/

    @Override
    public Object visit(StatementList statements) {
        StatementList r = new StatementList();
        for (Statement s : statements) {
            r.add((Statement) s.visit(this));
        }
        return r;
    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setLocalScope((LocalScope) programDeclaration.getLocalScope().visit(this));
        programDeclaration.setProgramBody((StatementList) programDeclaration.getProgramBody().visit(this));
        return programDeclaration;
    }

    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        return tsScalarValue;
        //return new ScalarValue<>(tsScalarValue.getDataType(), tsScalarValue.getValue());
    }


    @Override
    public Object visit(FunctionCall functionCall) {
        LinkedList<FunctionCall.Parameter> list = new LinkedList<>();
        for (FunctionCall.Parameter p : functionCall.getParameters()) {
            list.add(p);
        }
        functionCall.setParameters(list);
        return functionCall;
    }

    @Override
    public Object visit(ForStatement forStatement) {
        forStatement.setStart((Expression) forStatement.getStart().visit(this));
        forStatement.setStatements((StatementList) forStatement.getStatements().visit(this));
        forStatement.setStep((Expression) forStatement.getStep().visit(this));
        forStatement.setStop((Expression) forStatement.getStop().visit(this));
        return forStatement;
    }

    @Override
    public Object visit(IfStatement i) {
        LinkedList<GuardedStatement> guards = new LinkedList<>();
        for (GuardedStatement gc : i.getConditionalBranches()) {
            guards.add((GuardedStatement) gc.visit(this));
        }
        i.setConditionalBranches(guards);
        i.setElseBranch((StatementList) i.getElseBranch().visit(this));
        return i;
    }

    @Override
    public Object visit(CommentStatement commentStatement) {
        return commentStatement;
    }


    @Override
    public Object visit(GuardedStatement guardedStatement) {
        guardedStatement.setCondition((Expression) guardedStatement.getCondition().visit(this));
        guardedStatement.setStatements((StatementList) guardedStatement.getStatements().visit(this));
        return guardedStatement;
    }

    @Override
    public Object visit(FunctionCallStatement functionCallStatement) {
        functionCallStatement.setFunctionCall((FunctionCall)
                functionCallStatement.getFunctionCall().visit(this));
        return functionCallStatement;
    }

    @Override
    public Object visit(CaseStatement.Case aCase) {
        List<CaseConditions> v = this.<CaseConditions>visitList(aCase.getConditions());
        aCase.setConditions(v);
        aCase.setStatements((StatementList) aCase.getStatements().visit(this));
        return aCase;
    }

    private <T> List<T> visitList(List<? extends Visitable> list) {
        List l = new ArrayList();
        for (Visitable v : list)
            l.add((T) v.visit(this));
        return l;
    }

    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        return arrayTypeDeclaration;
    }

    @Override
    public Object visit(ExitStatement exitStatement) {
        return exitStatement;
    }

    @Override
    public Object visit(CaseConditions.Range range) {
        range.setStart((ScalarValue) range.getStart().visit(this));
        range.setStop((ScalarValue) range.getStop().visit(this));
        return super.visit(range);
    }

    @Override
    public Object visit(ConfigurationDeclaration configurationDeclaration) {
        return configurationDeclaration;
    }


    @Override
    public Object visit(LocalScope localScope) {
        return localScope;
    }

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        variableDeclaration.setInit((Initialization)
                variableDeclaration.getInit().visit(this));

        return variableDeclaration;
    }

    @Override
    public Object visit(ArrayInitialization initializations) {
        return initializations;
    }

    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        return enumerationTypeDeclaration;
    }

    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        TypeDeclarations td = new TypeDeclarations();
        for (TypeDeclaration t : typeDeclarations)
            td.add((TypeDeclaration) td.visit(this));
        return td;
    }

    @Override
    public Object visit(ExpressionList expressions) {
        ExpressionList expressionList = new ExpressionList();
        for (Expression e : expressions)
            expressionList.add((Expression) e.visit(this));
        return expressionList;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setLocalScope((LocalScope) functionDeclaration.getLocalScope().visit(this));
        functionDeclaration.setStatements((StatementList) functionDeclaration.getStatements().visit(this));
        return functionDeclaration;
    }

    @Override
    public Object visit(ResourceDeclaration resourceDeclaration) {
        return resourceDeclaration;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setLocalScope((LocalScope) functionBlockDeclaration.getLocalScope().visit(this));
        functionBlockDeclaration.setFunctionBody((StatementList) functionBlockDeclaration.getFunctionBody().visit(this));
        return functionBlockDeclaration;
    }

    @Override
    public Object visit(ReturnStatement returnStatement) {
        return returnStatement;
    }

    @Override
    public Object visit(StringTypeDeclaration stringTypeDeclaration) {
        return stringTypeDeclaration;
    }

    @Override
    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        return structureTypeDeclaration;
    }

    @Override
    public Object visit(SubRangeDataType subRangeDataType) {
        return subRangeDataType;
    }

    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return simpleTypeDeclaration;
    }


    @Override
    public Object visit(StructureInitialization structureInitialization) {
        return structureInitialization;
    }
}
