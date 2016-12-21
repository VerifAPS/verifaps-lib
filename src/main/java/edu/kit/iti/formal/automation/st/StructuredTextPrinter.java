package edu.kit.iti.formal.automation.st;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.operators.Operator;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.st.util.CodeWriter;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StructuredTextPrinter extends DefaultVisitor<Object> {
    private final StringLiterals literals;
    public CodeWriter sb = new CodeWriter();
    private boolean printComments;

    /**
     * <p>Constructor for StructuredTextPrinter.</p>
     */
    public StructuredTextPrinter() {
        this(SL_ST);
    }

    /**
     * <p>Constructor for StructuredTextPrinter.</p>
     *
     * @param sl_smv a {@link edu.kit.iti.formal.automation.st.StructuredTextPrinter.StringLiterals} object.
     */
    public StructuredTextPrinter(StringLiterals sl_smv) {
        literals = sl_smv;
    }

    /**
     * <p>isPrintComments.</p>
     *
     * @return a boolean.
     */
    public boolean isPrintComments() {
        return printComments;
    }

    /**
     * <p>Setter for the field <code>printComments</code>.</p>
     *
     * @param printComments a boolean.
     */
    public void setPrintComments(boolean printComments) {
        this.printComments = printComments;
    }

    /** {@inheritDoc} */
    @Override
    public Object defaultVisit(Visitable visitable) {
        throw new IllegalArgumentException("not implemented: " + visitable.getClass());
    }

    /**
     * <p>getString.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getString() {
        return sb.toString();
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExitStatement exitStatement) {
        sb.append(literals.exit()).append(literals.statement_separator());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(CaseConditions.IntegerCondition integerCondition) {
        sb.appendIdent();
        integerCondition.getValue().visit(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(CaseConditions.Enumeration enumeration) {
        if (enumeration.getStart() == enumeration.getStop()) {
            enumeration.getStart().visit(this);
        } else {
            enumeration.getStart().visit(this);
            sb.append("..");
            enumeration.getStop().visit(this);
        }

        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(BinaryExpression binaryExpression) {
        sb.append('(');
        binaryExpression.getLeftExpr().visit(this);
        sb.append(" ").append(literals.operator(binaryExpression.getOperator())).append(" ");
        binaryExpression.getRightExpr().visit(this);
        sb.append(')');
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(AssignmentStatement assignStatement) {
        sb.nl();
        assignStatement.getLocation().visit(this);
        sb.append(literals.assign());
        assignStatement.getExpression().visit(this);
        sb.append(";");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ConfigurationDeclaration configurationDeclaration) {
        return null;
    }


    /** {@inheritDoc} */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        sb.nl().append(enumerationTypeDeclaration.getTypeName()).append(" : ");

        sb.append("(");

        for (String s : enumerationTypeDeclaration.getAllowedValues())
            sb.append(s).append(" , ");

        sb.deleteLast(3);
        sb.append(");");

        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(RepeatStatement repeatStatement) {
        sb.nl();
        sb.append("REPEAT").increaseIndent();
        repeatStatement.getStatements().visit(this);

        sb.decreaseIndent().nl().append("UNTIL ");
        repeatStatement.getCondition().visit(this);
        sb.append("END_REPEAT");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(WhileStatement whileStatement) {
        sb.nl();
        sb.append("WHILE ");
        whileStatement.getCondition().visit(this);
        sb.append(" DO ").increaseIndent();
        whileStatement.getStatements().visit(this);
        sb.decreaseIndent().nl();
        sb.append("END_WHILE");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(UnaryExpression unaryExpression) {
        sb.append(literals.operator(unaryExpression.getOperator())).append(" ");
        unaryExpression.getExpression().visit(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(TypeDeclarations typeDeclarations) {

        if (typeDeclarations.size() > 0) {
            sb.append("TYPE").increaseIndent();
            for (TypeDeclaration decl : typeDeclarations) {
                decl.visit(this);
            }
            sb.decreaseIndent().nl().append("END_TYPE").nl().nl();
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(CaseStatement caseStatement) {

        sb.nl().append("CASE ");
        caseStatement.getExpression().visit(this);
        sb.append(" OF ").increaseIndent();

        for (CaseStatement.Case c : caseStatement.getCases()) {
            c.visit(this);
            sb.nl();
        }

        if (caseStatement.getElseCase().size() > 0) {
            sb.nl().append("ELSE ");
            caseStatement.getElseCase().visit(this);
        }

        sb.nl().decreaseIndent().appendIdent().append("END_CASE;");
        return null;
    }


    /**
     * <p>visit.</p>
     *
     * @param symbolicReference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     * @return a {@link java.lang.Object} object.
     */
    public Object visit(SymbolicReference symbolicReference) {
        sb.append(symbolicReference.getIdentifier());

        if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {
            sb.append('[');
            for (Expression expr : symbolicReference.getSubscripts()) {
                expr.visit(this);
                sb.append(',');
            }
            sb.deleteLast();
            sb.append(']');
        }

        if (symbolicReference.getSub() != null) {
            sb.append(".");
            //symbolicReference.getSub().visit(this);
        }

        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(StatementList statements) {
        for (Statement stmt : statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}");
            } else {
                stmt.visit(this);
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        sb.append("PROGRAM ").append(programDeclaration.getProgramName()).append('\n');

        programDeclaration.getLocalScope().visit(this);

        programDeclaration.getProgramBody().visit(this);
        sb.decreaseIndent().nl().append("END_PROGRAM").nl();
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        sb.append(literals.repr(tsScalarValue));
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ExpressionList expressions) {
        for (Expression e : expressions) {
            e.visit(this);
            sb.append(", ");
        }
        sb.deleteLast(2);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(FunctionCall functionCall) {
        // TODO
        sb.append(functionCall.getFunctionName()).append("(").append(")");
        return null;
    }

    /*
     * TODO to new ast visitor
     *
     * @Override public Object visit(CaseExpression caseExpression) {
     * sb.append("CASES(").increaseIndent(); for (CaseExpression.Case cas :
     * caseExpression.getCases()) { cas.getCondition().visit(this); sb.append(
     * " -> "); cas.getExpression().visit(this); sb.append(";").nl(); }
     * sb.append("ELSE -> "); caseExpression.getElseExpression().visit(this);
     * sb.append(")").decreaseIndent(); return null; }
     */
    /** {@inheritDoc} */
    @Override
    public Object visit(ForStatement forStatement) {
        sb.nl();
        sb.append("FOR ").append(forStatement.getVariable());
        sb.append(" := ");
        forStatement.getStart().visit(this);
        sb.append(" TO ");
        forStatement.getStop().visit(this);
        sb.append(" DO ").increaseIndent();
        forStatement.getStatements().visit(this);
        sb.decreaseIndent().nl();
        sb.append("END_FOR");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        sb.append("FUNCTION_BLOCK ").append(functionBlockDeclaration.getFunctionBlockName()).increaseIndent();

        functionBlockDeclaration.getLocalScope().visit(this);

        sb.nl();

        functionBlockDeclaration.getFunctionBody().visit(this);
        sb.decreaseIndent().nl().append("END_FUNCTION_BLOCK").nl().nl();
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(ReturnStatement returnStatement) {
        sb.appendIdent();
        sb.append("RETURN;");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(IfStatement ifStatement) {
        for (int i = 0; i < ifStatement.getConditionalBranches().size(); i++) {
            sb.nl();

            if (i == 0)
                sb.append("IF ");
            else
                sb.append("ELSEIF ");

            ifStatement.getConditionalBranches().get(i).getCondition().visit(this);

            sb.append(" THEN").increaseIndent();
            ifStatement.getConditionalBranches().get(i).getStatements().visit(this);
            sb.decreaseIndent();
        }

        if (ifStatement.getElseBranch().size() > 0) {
            sb.nl().append("ELSE").increaseIndent();
            ifStatement.getElseBranch().visit(this);
            sb.decreaseIndent();
        }
        sb.nl().append("END_IF;");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(FunctionCallStatement functionCallStatement) {
        sb.nl();
        sb.append(functionCallStatement.getFunctionCall().getFunctionName()).append("(");

        boolean params = false;
        for (FunctionCall.Parameter entry : functionCallStatement.getFunctionCall().getParameters()) {
            if (entry.getName() != null) {
                sb.append(entry.getName());
                if (entry.isOutput())
                    sb.append(" => ");
                else
                    sb.append(" := ");
            }

            entry.getExpression().visit(this);
            sb.append(", ");
            params = true;
        }

        if (params)
            sb.deleteLast(2);
        sb.append(");");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(CaseStatement.Case aCase) {
        sb.nl();
        for (CaseConditions cc : aCase.getConditions()) {
            cc.visit(this);
            sb.append(", ");
        }
        sb.deleteLast(2);
        sb.append(":");
        sb.increaseIndent();
        aCase.getStatements().visit(this);
        sb.decreaseIndent();
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        sb.append(simpleTypeDeclaration.getBaseTypeName());
        if (simpleTypeDeclaration.getInitializationValue() != null) {
            sb.append(" := ");
            simpleTypeDeclaration.getInitializationValue().visit(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(LocalScope localScope) {
        for (VariableDeclaration vd : localScope.getLocalVariables().values()) {
            vd.getDataType();
            sb.nl().append("VAR");

            if (vd.isInput())
                sb.append("_INPUT");
            if (vd.isOutput())
                sb.append("_OUTPUT");
            if (vd.isInOut())
                sb.append("_INOUT");

            if (vd.isExternal())
                sb.append("_EXTERNAL");
            if (vd.isGlobal())
                sb.append("_GLOBAL");

            sb.append(" ");

            if (vd.isConstant())
                sb.append(" CONSTANT ");

            if (vd.isRetain())
                sb.append("RETAIN");
            /*
             * else sb.append("NON_RETAIN");
			 */

            sb.append(" ");

            sb.append(vd.getName()).append(" : ");

            variableDataType(vd);

            if (vd.getInit() != null) {
                sb.append(" := ");
                vd.getInit().visit(this);
            }

            sb.append("; END_VAR ");

			/*sb.append("{*")
					.append((vd.isInput() ? "I" : "") + (vd.isOutput() ? "O" : "") + (vd.isLocal() ? "L" : "")
							+ (vd.is(READED) ? "R" : "r") + (vd.is(WRITTEN_TO) ? "W" : "w")
							+ (vd.is(WRITE_BEFORE_READ) ? "X" : "x")
							+ (vd.is(STSimplifier.PROGRAM_VARIABLE) ? "P" : "p"))
					.append("*}");*/
        }
        return null;
    }

    private void variableDataType(VariableDeclaration vd) {
        if (vd.getDataType() instanceof IECArray) {
            IECArray dataType = (IECArray) vd.getDataType();
            sb.append(" ARRAY[");
            for (Range range : dataType.getRanges()) {
                range.getStart().visit(this);
                sb.append("..");
                range.getStop().visit(this);
                sb.append(",");
            }
            sb.deleteLast();
            sb.append("] OF ").append(dataType.getFieldType().getName());
        } else {
            sb.append(vd.getDataTypeName());
        }
    }

    /** {@inheritDoc} */
    @Override
    public Object visit(CommentStatement commentStatement) {
        if (printComments) {
            sb.nl();
            sb.append(literals.comment_open());
            sb.append(commentStatement.getComment());
            sb.append(literals.comment_close());
        }
        return null;

    }

    /**
     * <p>clear.</p>
     */
    public void clear() {
        sb = new CodeWriter();
    }

    public static class StringLiterals {

        public static StringLiterals create() {
            return new StringLiterals();
        }

        public String operator(Operator operator) {
            return operator.symbol();
        }

        public String assign() {
            return " := ";
        }

        public String statement_separator() {
            return ";";
        }

        public String exit() {
            return "EXIT";
        }

        public String operator(UnaryOperator operator) {
            return operator.symbol();
        }

        public String comment_close() {
            return " *)";
        }

        public String comment_open() {
            return "(* ";
        }

        public String repr(ScalarValue<? extends Any, ?> sv) {
            return sv.getDataType().repr(sv.getValue());
        }
    }

    /** Constant <code>SL_ST</code> */
    public static StringLiterals SL_ST = StringLiterals.create();
    /** Constant <code>SL_SMV</code> */
    public static StringLiterals SL_SMV = new StringLiterals() {
        @Override
        public String operator(UnaryOperator operator) {
            /*switch (operator) {
                case MINUS:
                    return "-";
                case NEGATE:
                    return "!";
            }*/
            return "<<unknown ue operator>>";
        }

        @Override
        public String operator(Operator operator) {
            /*switch (operator) {
                case AND:
                    return "&";
                case OR:
                    return "|";
                case XOR:
                    return "xor";
                case NOT_EQUALS:
                    return "!=";
            }*/
            return operator.symbol();
        }

        @Override
        public String repr(ScalarValue<? extends Any, ?> sv) {
            if (sv.getDataType() instanceof AnyUInt) {
                AnyInt dataType = (AnyInt) sv.getDataType();
                return String.format("0ud%d_%d", 13, sv.getValue());
            }

            if (sv.getDataType() instanceof AnySignedInt) {
                AnyInt dataType = (AnyInt) sv.getDataType();
                return String.format("0sd%d_%d", 14, sv.getValue());
            }

            if (sv.getDataType() instanceof EnumerateType) {
                EnumerateType dataType = (EnumerateType) sv.getDataType();
                return sv.getValue().toString();
            }

            return super.repr(sv);
        }
    };

    /**
     * <p>setCodeWriter.</p>
     *
     * @param cw a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public void setCodeWriter(CodeWriter cw) {
        this.sb = cw;
    }
}
