package edu.kit.iti.formal.automation.util;

import edu.kit.iti.formal.automation.ast.*;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;

/**
 * Created by weigl on 08/09/14.
 */
public class PythonPrinter extends AstVisitor<Object> {
    private boolean inClass;

    CodeWriter cw = new CodeWriter();


    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        cw.nl();
        assignmentStatement.getVariable().visit(this);
        cw.append(" = ");
        assignmentStatement.getExpression().visit(this);
        return null;
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        binaryExpression.getLeftExpr().visit(this);

        cw.append(" ").append(binaryExpression.getOperator().symbol.toLowerCase()).append(" ");
        binaryExpression.getRightExpr().visit(this);
        return null;
    }

    @Override
    public Object visit(RepeatStatement repeatStatement) {
        repeatStatement.getStatements().visit(this);
        cw.appendIdent().append("while ");
        repeatStatement.getCondition().visit(this);
        cw.append(":");
        repeatStatement.getStatements().visit(this);
        return null;
    }

    @Override
    public Object visit(WhileStatement whileStatement) {
        cw.nl().append("while ");
        whileStatement.getCondition().visit(this);
        cw.append(":");
        whileStatement.getStatements().visit(this);
        return null;
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        cw.append(unaryExpression.getOperator().symbol);
        unaryExpression.getExpression().visit(this);
        return null;
    }

    private Expression caseExpression;

    @Override
    public Object visit(CaseStatement caseStatement) {
        String s = "if ";

        caseExpression = caseStatement.getExpression();

        for (CaseStatement.Case esac : caseStatement.getCases()) {
            cw.nl().nl();
            cw.append(s);
            esac.visit(this);
            cw.append(":");
            cw.increaseIndent();
            esac.getStatements().visit(this);
            cw.decreaseIndent();
            s = "elif ";
        }

        if (caseStatement.getElseCase().size() > 0) {
            cw.append("else:")
                    .increaseIndent();
            caseStatement.getElseCase().visit(this);
            cw.decreaseIndent();
        }
        return null;
    }


    @Override
    public Object visit(CaseStatement.Case aCase) {
        for (CaseConditions cc : aCase.getConditions()) {
            cc.visit(this);
            cw.append(" and ");
        }
        cw.deleteLast(5);
        return null;
    }

    @Override
    public Object visit(CaseConditions.Range range) {
        caseExpression.visit(this);
        cw.append(" in range(");
        range.getStart().visit(this);
        cw.append(",");
        range.getStop().visit(this);
        cw.append(")");
        return null;
    }


    @Override
    public Object visit(CaseConditions.IntegerCondition integerCondition) {
        caseExpression.visit(this);
        cw.append(" == ");
        integerCondition.getValue().visit(this);
        return null;
    }

    @Override
    public Object visit(CaseConditions.Enumeration enumeration) {
        caseExpression.visit(this);
        if (enumeration.getStart() == enumeration.getStop()) {
            cw.append(" == ");
            enumeration.getStart().visit(this);
        } else {
            cw.append(" in range(");
            enumeration.getStart().visit(this);
            cw.append(",");
            enumeration.getStop().visit(this);
            cw.append(")");
        }
        return null;
    }

    @Override
    public Object visit(ExpressionList expressions) {
        return super.visit(expressions);
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        boolean temp = inClass;
        inClass = false;


        if (temp) {
            cw.append("self.");
        }
        cw.append(symbolicReference.getIdentifier());

        if (symbolicReference.getSubscripts() != null) {
            for (Expression e : symbolicReference.getSubscripts()) {
                cw.append("[");
                e.visit(this);
                cw.append("]");
            }
        }

        if (symbolicReference.getSub() != null) {
            cw.append(".");
            symbolicReference.getSub().visit(this);
        }

        inClass = temp;
        return null;
    }


    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        inClass = true;
        cw.nl().appendf("class %s(object):", programDeclaration.getProgramName());
        cw.increaseIndent();
        cw.nl().append("def __init__(self):");
        cw.increaseIndent();
        programDeclaration.getScope().visit(this);
        cw.decreaseIndent();

        cw.nl().nl().append("def __call__(self):");
        cw.increaseIndent();
        programDeclaration.getProgramBody().visit(this);
        cw.decreaseIndent();
        cw.decreaseIndent();
        cw.append("\n\n");
        inClass = false;

        return null;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        cw.nl().appendf("def %s():", functionDeclaration.getBlockName());
        cw.increaseIndent();
        // TODO
        cw.decreaseIndent();
        cw.append("\n\n");
        return null;
    }

    @Override
    public Object visit(ForStatement forStatement) {
        cw.nl().appendf("for %s in range(", forStatement.getVariable());
        forStatement.getStart().visit(this);
        cw.append(",");
        forStatement.getStop().visit(this);
        if (forStatement.getStep() != null) {
            cw.append(",");
            forStatement.getStep().visit(this);
        }
        cw.append("):");
        cw.increaseIndent();
        forStatement.getStatements().visit(this);
        cw.decreaseIndent();
        return null;
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        inClass = true;
        cw.nl().appendf("class %s(object):", functionBlockDeclaration.getBlockName());
        cw.increaseIndent();
        cw.nl().append("def __init__(self):");
        cw.increaseIndent();
        functionBlockDeclaration.getScope().visit(this);
        cw.decreaseIndent();

        cw.nl().nl().append("def __call__(self):");
        cw.increaseIndent();
        functionBlockDeclaration.getFunctionBody().visit(this);
        cw.decreaseIndent();
        cw.decreaseIndent();
        cw.append("\n\n");
        inClass = false;
        return null;
    }

    @Override
    public Object visit(IfStatement ifStatement) {
        cw.nl();
        String S = "if ";


        for (GuardedStatement gs : ifStatement.getConditionalBranches()) {
            cw.nl().append(S);
            gs.getCondition().visit(this);
            cw.append(":").increaseIndent();
            gs.getStatements().visit(this);
            cw.decreaseIndent();
            S = "elif ";
        }

        if (!ifStatement.getElseBranch().isEmpty()) {
            cw.nl().append("else:").increaseIndent();
            ifStatement.getElseBranch().visit(this);
            cw.decreaseIndent();
        }

        return null;
    }

    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        cw.nl().appendf("self.%s = ", variableDeclaration.getName());
        if (variableDeclaration.getInit() != null)
            variableDeclaration.getInit().visit(this);
        else
            cw.append("None");
        return null;
    }

    @Override
    public Object visit(ExitStatement exitStatement) {
        cw.append("break");
        return null;
    }

    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        cw.nl();
        cw.appendf("class %s(object):", enumerationTypeDeclaration.getTypeName());
        cw.increaseIndent();
        int i = 0;
        for (String value : enumerationTypeDeclaration.getAllowedValues()) {
            cw.nl();
            if (value.equals(enumerationTypeDeclaration.getInitializationValue()))
                cw.appendf("%s = %d", value, 0);
            else
                cw.appendf("%s = %d", value, ++i);

        }

        cw.decreaseIndent();
        cw.nl();
        return null;
    }

    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        if (tsScalarValue.getDataType() instanceof EnumerateType) {
            EnumerateType dataType = (EnumerateType) tsScalarValue.getDataType();
            cw.appendf("%s.%s", dataType.getName(), tsScalarValue.getValue());
        } else if (tsScalarValue.getDataType() instanceof AnyBit.Bool) {
            String s = tsScalarValue.getDataType().repr(tsScalarValue.getValue());
            String t = Character.toUpperCase(s.charAt(0)) +
                    s.substring(1).toLowerCase();
            cw.append(t);
        } else {
            cw.append(tsScalarValue.getDataType().repr(tsScalarValue.getValue()));
        }

        return null;
    }


    @Override
    public Object visit(ReturnStatement returnStatement) {
        cw.append("return");
        return null;
    }

    @Override
    public Object visit(FunctionCallStatement functionCallStatement) {
        cw.nl().appendf("self.%s()", functionCallStatement.getFunctionCall().getFunctionName());
        return null;
    }

    @Override
    public Object visit(CommentStatement commentStatement) {
        cw.nl().append("#").append(commentStatement.comment);
        return null;
    }

    public String getOutput() {
        return cw.toString();
    }
}
