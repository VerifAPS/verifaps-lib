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

import edu.kit.iti.formal.automation.datatypes.IECArray;
import edu.kit.iti.formal.automation.datatypes.values.Value;
import edu.kit.iti.formal.automation.operators.Operator;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.CodeWriter;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import org.antlr.v4.runtime.Token;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
public class StructuredTextPrinter extends DefaultVisitor<Object> {
    /**
     * Constant <code>SL_ST</code>
     */
    public static StringLiterals SL_ST = StringLiterals.create();
    /**
     * Constant <code>SL_SMV</code>
     */
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

        /*
        @Override
        public String repr(ScalarValue<? extends Any, ?> sv) {
            if (sv.getDataType() instanceof AnyUnsignedInt) {
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
        */
    };
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

    /**
     * {@inheritDoc}
     */
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

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExitStatement exitStatement) {
        sb.append(literals.exit()).append(literals.statement_separator());
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.IntegerCondition integerCondition) {
        sb.appendIdent();
        integerCondition.getValue().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.Enumeration enumeration) {
        if (enumeration.getStart() == enumeration.getStop()) {
            enumeration.getStart().accept(this);
        } else {
            enumeration.getStart().accept(this);
            sb.append("..");
            enumeration.getStop().accept(this);
        }

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(BinaryExpression binaryExpression) {
        sb.append('(');
        binaryExpression.getLeftExpr().accept(this);
        sb.append(" ").append(literals.operator(binaryExpression.getOperator())).append(" ");
        binaryExpression.getRightExpr().accept(this);
        sb.append(')');
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(AssignmentStatement assignStatement) {
        sb.nl();
        assignStatement.getLocation().accept(this);
        if (assignStatement.isAssignmentAttempt())
            sb.append(literals.assignmentAttempt());
        else
            sb.append(literals.assign());
        assignStatement.getExpression().accept(this);
        sb.append(";");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ConfigurationDeclaration configurationDeclaration) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        sb.nl().append(enumerationTypeDeclaration.getTypeName()).append(" : ");

        sb.append("(");

        for (Token s : enumerationTypeDeclaration.getAllowedValues())
            sb.append(s.getText()).append(" , ");

        sb.deleteLast(3);
        sb.append(");");

        return null;
    }

    @Override
    public Object visit(IdentifierInitializer init) {
        sb.append(init.getValue());
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(RepeatStatement repeatStatement) {
        sb.nl();
        sb.append("REPEAT").increaseIndent();
        repeatStatement.getStatements().accept(this);

        sb.decreaseIndent().nl().append("UNTIL ");
        repeatStatement.getCondition().accept(this);
        sb.append("END_REPEAT");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(WhileStatement whileStatement) {
        sb.nl();
        sb.append("WHILE ");
        whileStatement.getCondition().accept(this);
        sb.append(" DO ").increaseIndent();
        whileStatement.getStatements().accept(this);
        sb.decreaseIndent().nl();
        sb.append("END_WHILE");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(UnaryExpression unaryExpression) {
        sb.append(literals.operator(unaryExpression.getOperator())).append(" ");
        unaryExpression.getExpression().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(TypeDeclarations typeDeclarations) {

        if (typeDeclarations.size() > 0) {
            sb.append("TYPE ").increaseIndent();
            for (TypeDeclaration decl : typeDeclarations) {
                decl.accept(this);
            }
            sb.decreaseIndent().nl().append("END_TYPE").nl().nl();
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement caseStatement) {

        sb.nl().append("CASE ");
        caseStatement.getExpression().accept(this);
        sb.append(" OF ").increaseIndent();

        for (CaseStatement.Case c : caseStatement.getCases()) {
            c.accept(this);
            sb.nl();
        }

        if (caseStatement.getElseCase().size() > 0) {
            sb.nl().append("ELSE ");
            caseStatement.getElseCase().accept(this);
        }

        sb.nl().decreaseIndent().appendIdent().append("END_CASE;");
        return null;
    }

    /**
     * <p>accept.</p>
     *
     * @param symbolicReference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     * @return a {@link java.lang.Object} object.
     */
    public Object visit(SymbolicReference symbolicReference) {
        sb.append(symbolicReference.getIdentifier());

        for (int i = 0; i < symbolicReference.getDerefCount(); i++)
            sb.append("^");

        if (symbolicReference.getSubscripts() != null && !symbolicReference.getSubscripts().isEmpty()) {
            sb.append('[');
            for (Expression expr : symbolicReference.getSubscripts()) {
                expr.accept(this);
                sb.append(',');
            }
            sb.deleteLast();
            sb.append(']');
        }

        if (symbolicReference.getSub() != null) {
            sb.append(".");
            symbolicReference.getSub().accept(this);
        }

        return null;
    }

    /** {@inheritDoc} *
     @Override public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
     sb.append(literals.repr(tsScalarValue));
     return null;
     }*/

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StatementList statements) {
        for (Statement stmt : statements) {
            if (stmt == null) {
                sb.append("{*ERROR: stmt null*}");
            } else {
                stmt.accept(this);
            }
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        sb.append("PROGRAM ").append(programDeclaration.getProgramName()).append('\n');

        programDeclaration.getLocalScope().accept(this);

        programDeclaration.getProgramBody().accept(this);
        sb.decreaseIndent().nl().append("END_PROGRAM").nl();
        return null;
    }

    /*
     * TODO to new ast visitor
     *
     * @Override public Object accept(CaseExpression caseExpression) {
     * sb.append("CASES(").increaseIndent(); for (CaseExpression.Case cas :
     * caseExpression.getCases()) { cas.getCondition().accept(this); sb.append(
     * " -> "); cas.getExpression().accept(this); sb.append(";").nl(); }
     * sb.append("ELSE -> "); caseExpression.getElseExpression().accept(this);
     * sb.append(")").decreaseIndent(); return null; }
     */

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExpressionList expressions) {
        for (Expression e : expressions) {
            e.accept(this);
            sb.append(", ");
        }
        sb.deleteLast(2);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(Invocation invocation) {
        sb.append(invocation.getCalleeName()).append("(");

        boolean params = false;
        for (Invocation.Parameter entry : invocation.getParameters()) {
            if (entry.getName() != null) {
                sb.append(entry.getName());
                if (entry.isOutput())
                    sb.append(" => ");
                else
                    sb.append(" := ");
            }

            entry.getExpression().accept(this);
            sb.append(", ");
            params = true;
        }

        if (params)
            sb.deleteLast(2);
        sb.append(");");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ForStatement forStatement) {
        sb.nl();
        sb.append("FOR ").append(forStatement.getVariable());
        sb.append(" := ");
        forStatement.getStart().accept(this);
        sb.append(" TO ");
        forStatement.getStop().accept(this);
        sb.append(" DO ").increaseIndent();
        forStatement.getStatements().accept(this);
        sb.decreaseIndent().nl();
        sb.append("END_FOR");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        sb.append("FUNCTION_BLOCK ");

        if (functionBlockDeclaration.isFinal_())
            sb.append("FINAL ");
        if (functionBlockDeclaration.isAbstract_())
            sb.append("ABSTRACT ");

        sb.append(functionBlockDeclaration.getName());

        String parent = functionBlockDeclaration.getParent().getIdentifier();
        if (parent != null)
            sb.append(" EXTENDS ").append(parent);

        String interfaces = functionBlockDeclaration.getInterfaces().stream()
                .map(i -> i.getIdentifier())
                .collect(Collectors.joining(", "));
        if (!interfaces.isEmpty())
            sb.append(" IMPLEMENTS ").append(interfaces);

        sb.increaseIndent().nl();

        functionBlockDeclaration.getLocalScope().accept(this);

        sb.nl();

        functionBlockDeclaration.getMethods().forEach(m -> m.accept(this));

        sb.nl();

        functionBlockDeclaration.getFunctionBody().accept(this);

        sb.decreaseIndent().nl().append("END_FUNCTION_BLOCK").nl().nl();
        return null;
    }

    @Override
    public Object visit(InterfaceDeclaration interfaceDeclaration) {
        sb.append("INTERFACE ").append(interfaceDeclaration.getName());

        String extendsInterfaces = interfaceDeclaration.getExtendsInterfaces().stream()
                .map(i -> i.getIdentifier())
                .collect(Collectors.joining(", "));
        if (!extendsInterfaces.isEmpty())
            sb.append(" EXTENDS ").append(extendsInterfaces);

        sb.increaseIndent().nl();

        interfaceDeclaration.getLocalScope().accept(this);

        interfaceDeclaration.getMethods().forEach(m -> m.accept(this));

        sb.decreaseIndent().nl().append("END_INTERFACE").nl().nl();
        return null;
    }

    @Override
    public Object visit(ClassDeclaration clazz) {
        sb.append("CLASS ");

        if (clazz.isFinal_())
            sb.append("FINAL ");
        if (clazz.isAbstract_())
            sb.append("ABSTRACT ");

        sb.append(clazz.getName());

        String parent = clazz.getParent().getIdentifier();
        if (parent != null)
            sb.append(" EXTENDS ").append(parent);

        String interfaces = clazz.getInterfaces().stream()
                .map(i -> i.getIdentifier())
                .collect(Collectors.joining(", "));
        if (!interfaces.isEmpty())
            sb.append(" IMPLEMENTS ").append(interfaces);

        sb.increaseIndent().nl();

        clazz.getLocalScope().accept(this);

        clazz.getMethods().forEach(m -> m.accept(this));

        sb.decreaseIndent().nl().append("END_CLASS").nl().nl();
        return null;
    }

    @Override
    public Object visit(MethodDeclaration method) {
        sb.append("METHOD ");

        if (method.isFinal_())
            sb.append("FINAL ");
        if (method.isAbstract_())
            sb.append("ABSTRACT" );
        if (method.isOverride())
            sb.append("OVERRIDE ");

        sb.append(method.getAccessSpecifier() + " ");

        sb.append(method.getIdentifier());

        String returnType = method.getReturnTypeName();
        if (!returnType.isEmpty())
            sb.append(" : " + returnType);

        sb.increaseIndent().nl();

        method.getLocalScope().accept(this);

        method.getStatements().accept(this);

        sb.decreaseIndent().nl().append("END_METHOD").nl().nl();
        return null;
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        sb.append("FUNCTION ").append(functionDeclaration.getFunctionName());

        String returnType = functionDeclaration.getReturnTypeName();
        if (!(returnType == null || returnType.isEmpty()))
            sb.append(" : " + returnType);

        sb.increaseIndent().nl();

        functionDeclaration.getLocalScope().accept(this);

        functionDeclaration.getStatements().accept(this);

        sb.decreaseIndent().nl().append("END_FUNCTION").nl().nl();
        return null;
    }

    @Override
    public Object visit(ReferenceSpecification referenceSpecification) {
        sb.append("REF_TO ");
        referenceSpecification.getRefTo().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ReturnStatement returnStatement) {
        sb.appendIdent();
        sb.append("RETURN;");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(IfStatement ifStatement) {
        for (int i = 0; i < ifStatement.getConditionalBranches().size(); i++) {
            sb.nl();

            if (i == 0)
                sb.append("IF ");
            else
                sb.append("ELSEIF ");

            ifStatement.getConditionalBranches().get(i).getCondition().accept(this);

            sb.append(" THEN").increaseIndent();
            ifStatement.getConditionalBranches().get(i).getStatements().accept(this);
            sb.decreaseIndent();
        }

        if (ifStatement.getElseBranch().size() > 0) {
            sb.nl().append("ELSE").increaseIndent();
            ifStatement.getElseBranch().accept(this);
            sb.decreaseIndent();
        }
        sb.nl().append("END_IF");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(InvocationStatement fbc) {
        sb.nl();
        fbc.getInvocation().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement.Case aCase) {
        sb.nl();
        for (CaseCondition cc : aCase.getConditions()) {
            cc.accept(this);
            sb.append(", ");
        }
        sb.deleteLast(2);
        sb.append(":");
        sb.increaseIndent();
        aCase.getStatements().accept(this);
        sb.decreaseIndent();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        sb.append(simpleTypeDeclaration.getBaseTypeName());
        if (simpleTypeDeclaration.getInitialization() != null) {
            sb.append(" := ");
            simpleTypeDeclaration.getInitialization().accept(this);
        }
        return null;
    }

    @Override
    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        sb.append(structureTypeDeclaration.getTypeName());
        sb.append(": STRUCT").nl().increaseIndent();
        structureTypeDeclaration.getFields().accept(this);
        sb.decreaseIndent().append("END_STRUCT;").nl();
        return null;
    }

    @Override
    public Object visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        sb.append(subRangeTypeDeclaration.getTypeName());
        sb.append(": ").append(subRangeTypeDeclaration.getBaseTypeName());
        sb.append("(");
        subRangeTypeDeclaration.getRange().getStart().accept(this);
        sb.append(" .. ");
        subRangeTypeDeclaration.getRange().getStop().accept(this);
        sb.append(")");
        if (subRangeTypeDeclaration.getInitialization() != null) {
            sb.append(" := ");
            subRangeTypeDeclaration.getInitialization().accept(this);
        }
        sb.append(";");
        return null;
    }

    private void variableDataType(VariableDeclaration vd) {
        if (vd.getDataType() instanceof IECArray) {
            IECArray dataType = (IECArray) vd.getDataType();
            sb.append(" ARRAY[");
            for (Range range : dataType.getRanges()) {
                range.getStart().accept(this);
                sb.append("..");
                range.getStop().accept(this);
                sb.append(",");
            }
            sb.deleteLast();
            sb.append("] OF ").append(dataType.getFieldType().getName());
        } else {
            sb.append(vd.getDataTypeName());
        }
    }

    /**
     * {@inheritDoc}
     */
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
     * {@inheritDoc}
     */
    @Override
    public Object visit(Literal literal) {
        sb.append(literal.getText());
        return null;

    }

    @Override
    public Object visit(ArrayInitialization initializations) {
        sb.append("[");
        initializations.forEach(i -> {
            i.accept(this);
            sb.append(", ");
        });
        // Added an extra ", "
        sb.deleteLast(2);
        sb.append("]");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(LocalScope localScope) {
        List<VariableDeclaration> variables = localScope.getLocalVariables().values()
                .stream().collect(Collectors.toList());
        Collections.sort(variables, VariableDeclaration::compareTo);
        for (VariableDeclaration vd : variables) {
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
                vd.getInit().accept(this);
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

    public Object visit(StructureInitialization structureInitialization) {
        sb.append("(");
        structureInitialization.getInitValues().entrySet().stream().forEach(initialization -> {
            sb.append(initialization.getKey()).append(" := ");
            initialization.getValue().accept(this);
            sb.append(", ");
        });
        // Added an extra ", "
        sb.deleteLast(2);
        sb.append(")");
        return null;
    }

    /**
     * <p>clear.</p>
     */
    public void clear() {
        sb = new CodeWriter();
    }

    /**
     * <p>setCodeWriter.</p>
     *
     * @param cw a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public void setCodeWriter(CodeWriter cw) {
        this.sb = cw;
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

        public String assignmentAttempt() {
            return " ?= ";
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

        public String repr(Value sv) {
            return sv.getDataType().repr(sv.getValue());
        }

    }
}
