package edu.kit.iti.formal.automation.parser;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import com.google.common.collect.Streams;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.TransitionDeclaration;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (23.06.17)
 */
public class IECParseTreeToAST extends IEC61131ParserBaseVisitor<Object> {
    private VariableBuilder gather;
    private SFCDeclaration sfc;
    private StepDeclaration stepDeclaration;

    @Override
    public TopLevelElements visitStart(
            IEC61131Parser.StartContext ctx) {
        TopLevelElements ast = new TopLevelElements();
        ast.setRuleContext(ctx);
        ctx.library_element_declaration().forEach(l -> {
            TopLevelElement accept = (TopLevelElement) l.accept(this);
            if (accept != null)
                ast.add(accept);
        });
        return ast;
    }

    @Override
    public Literal visitCast(IEC61131Parser.CastContext ctx) {
        Literal ast = Literal.enumerate(ctx.CAST_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitInteger(IEC61131Parser.IntegerContext ctx) {
        Literal ast = Literal.integer(ctx.INTEGER_LITERAL().getSymbol(),
                ctx.MINUS() != null);
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitBits(IEC61131Parser.BitsContext ctx) {
        Literal ast = Literal.word(ctx.BITS_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitReal(IEC61131Parser.RealContext ctx) {
        Literal ast = Literal.real(ctx.REAL_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitString(IEC61131Parser.StringContext ctx) {
        Literal ast =
                ctx.STRING_LITERAL() != null
                        ? Literal.string(ctx.STRING_LITERAL().getSymbol(), false)
                        : Literal.string(ctx.WSTRING_LITERAL().getSymbol(), false);
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitTime(IEC61131Parser.TimeContext ctx) {
        Literal ast = Literal.time(ctx.TIME_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitTimeofday(
            IEC61131Parser.TimeofdayContext ctx) {
        Literal ast = Literal.timeOfDay(ctx.TOD_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitDate(IEC61131Parser.DateContext ctx) {
        Literal ast = Literal.date(ctx.DATE_LITERAL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitDatetime(IEC61131Parser.DatetimeContext ctx) {
        Literal ast = Literal.dateAndTime(ctx.DATETIME().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitData_type_declaration(
            IEC61131Parser.Data_type_declarationContext ctx) {
        TypeDeclarations ast = new TypeDeclarations();
        ast.setRuleContext(ctx);
        for (int i = 0; i < ctx.type_declaration().size(); i++) {
            TypeDeclaration t = (TypeDeclaration) ctx.type_declaration(i).accept(this);
            ast.add(t);
            t.setTypeName(ctx.IDENTIFIER(i).getText());
        }
        //Utils.setPosition(ast, ctx.TYPE, ctx.END_TYPE);
        return ast;
    }

    @Override
    public Object visitData_type_name(
            IEC61131Parser.Data_type_nameContext ctx) {
        SimpleTypeDeclaration td = new SimpleTypeDeclaration();
        td.setRuleContext(ctx);
        td.setBaseTypeName(ctx.non_generic_type_name().getText());
        return td;
    }

    private <T> List<T> allOf(List<? extends ParserRuleContext> ctx) {
        return ctx.stream().map(a -> (T) a.accept(this))
                .collect(Collectors.toList());
    }

    private <T> T oneOf(ParserRuleContext... children) {
        Function<ParserRuleContext, T> call = (ParserRuleContext r) ->
                r != null ? (T) r.accept(this) : null;
        for (ParserRuleContext c : children) {
            T a = call.apply(c);
            if (a != null)
                return a;
        }
        return null;
    }

    @Override
    public Object visitType_declaration(
            IEC61131Parser.Type_declarationContext ctx) {
        TypeDeclaration<Initialization> t = oneOf(
                ctx.array_specification(), ctx.enumerated_specification(),
                ctx.string_type_declaration(), ctx.subrange_spec_init(),
                ctx.structure_declaration(), ctx.data_type_name());

        if (ctx.i != null) {
            t.setInitialization((Initialization) ctx.i.accept(this));
        }
        return t;
    }

    @Override
    public Object visitInitializations_identifier(
            IEC61131Parser.Initializations_identifierContext ctx) {
        IdentifierInitializer ast = new IdentifierInitializer(
                ctx.IDENTIFIER().getText());
        return ast;
    }

    @Override
    public Object visitSubrange_spec_init(
            IEC61131Parser.Subrange_spec_initContext ctx) {
        SubRangeTypeDeclaration ast = new SubRangeTypeDeclaration();
        ast.setRuleContext(ctx);

        ast.setBaseTypeName(ctx.integer_type_name().getText());
        ast.setRange((Range) ctx.subrange().accept(this));
        //Utils.setPosition(ast, ctx.integer_type_name.ctx, ctx.RPAREN);
        return ast;
    }

    @Override
    public Object visitSubrange(IEC61131Parser.SubrangeContext ctx) {
        return new Range((Literal) ctx.c.accept(this), (Literal) ctx.d.accept(this));
    }

    @Override
    public Object visitEnumerated_specification(
            IEC61131Parser.Enumerated_specificationContext ctx) {
        EnumerationTypeDeclaration ast = new EnumerationTypeDeclaration();
        ast.setRuleContext(ctx);


        for (int i = 0; i < ctx.name.size(); i++) {
            ast.addValue(ctx.name.get(i));
            if (ctx.integer(i) != null) {
                ast.setInt((Literal) ctx.integer(i).accept(this));
            }
        }

        if (ctx.basename != null) {
            ast.setBaseTypeName(ctx.basename.getText());
        }
        return ast;
    }

    @Override
    public Object visitArray_specification(
            IEC61131Parser.Array_specificationContext ctx) {
        ArrayTypeDeclaration ast = new ArrayTypeDeclaration();
        //Utils.setPosition(ast, ctx.ARRAY(), ctx.non_generic_type_name.ctx);
        ast.setBaseTypeName(ctx.non_generic_type_name().getText());
        for (IEC61131Parser.SubrangeContext src : ctx.ranges) {
            ast.addSubRange((Range) src.accept(this));
        }
        return ast;
    }

    @Override
    public Object visitArray_initialization(
            IEC61131Parser.Array_initializationContext ctx) {
        ArrayInitialization ast = new ArrayInitialization();
        ast.setRuleContext(ctx);

        ctx.array_initial_elements().forEach(a -> a.accept(this));
        return ast;
    }

    @Override
    public Object visitArray_initial_elements(
            IEC61131Parser.Array_initial_elementsContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitArray_initial_element(
            IEC61131Parser.Array_initial_elementContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitStructure_declaration(
            IEC61131Parser.Structure_declarationContext ctx) {
        StructureTypeDeclaration ast = new StructureTypeDeclaration();
        for (int i = 0; i < ctx.type_declaration().size(); i++) {
            ast.addField(ctx.IDENTIFIER(i).getText(),
                    (TypeDeclaration) ctx.type_declaration(i).accept(this));
        }
        return ast;
    }

    @Override
    public Object visitStructure_initialization(
            IEC61131Parser.Structure_initializationContext ctx) {
        StructureInitialization ast = new StructureInitialization();
        ast.setRuleContext(ctx);

        ast.addField(ctx.I.getText(), (Initialization) ctx.i.accept(this));
        return ast;
    }

    @Override
    public Object visitString_type_declaration(
            IEC61131Parser.String_type_declarationContext ctx) {
        StringTypeDeclaration ast = new StringTypeDeclaration();
        ast.setRuleContext(ctx);

        ast.setBaseTypeName(ctx.baseType.getText());
        if (ctx.integer() != null) {
            ast.setSize((Literal) ctx.integer().accept(this));
        }
        return ast;
    }

    @Override
    public List<String> visitIdentifier_list(
            IEC61131Parser.Identifier_listContext ctx) {
        return ctx.names.stream().map(Token::getText)
                .collect(Collectors.toList());
    }

    @Override
    public Object visitFunction_declaration(
            IEC61131Parser.Function_declarationContext ctx) {
        FunctionDeclaration ast = new FunctionDeclaration();
        ast.setRuleContext(ctx);
        ast.setFunctionName(ctx.identifier.getText());
        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        if (ctx.returnET != null) {
            ast.setReturnTypeName(ctx.returnET.getText());
        } else {
            ast.setReturnTypeName(ctx.returnID.getText());
        }
        ast.setFunctionName(ctx.identifier.getText());
        ast.setStatements((StatementList) ctx.body.accept(this));
        return ast;
    }

    @Override
    public Object visitVar_decls(
            IEC61131Parser.Var_declsContext ctx) {
        LocalScope localScope = new LocalScope();
        gather = localScope.builder();
        ctx.var_decl().forEach(vd -> {
            vd.accept(this);
        });
        gather = null;
        return localScope;
    }

    @Override
    public Object visitVar_decl(IEC61131Parser.Var_declContext ctx) {
        gather.clear();
        ctx.variable_keyword().accept(this);
        Streams.forEachPair(ctx.identifier_list().stream(),
                ctx.type_declaration().stream(), (id, type) -> {
                    gather.identifiers((List<String>) id.accept(this))
                            .type((TypeDeclaration) type.accept(this)).close();
                });
        return null;
    }

    @Override
    public Object visitVariable_keyword(
            IEC61131Parser.Variable_keywordContext ctx) {
        if (ctx.VAR() != null) {
            gather.push(VariableDeclaration.LOCAL);
        }
        if (ctx.VAR_INPUT() != null) {
            gather.push(VariableDeclaration.INPUT);
        }
        if (ctx.VAR_OUTPUT() != null) {
            gather.push(VariableDeclaration.OUTPUT);
        }
        if (ctx.VAR_IN_OUT() != null) {
            gather.push(VariableDeclaration.INOUT);
        }
        if (ctx.VAR_EXTERNAL() != null) {
            gather.push(VariableDeclaration.EXTERNAL);
        }
        if (ctx.VAR_GLOBAL() != null) {
            gather.push(VariableDeclaration.GLOBAL);
        }

        if (ctx.CONSTANT() != null) {
            gather.mix(VariableDeclaration.CONSTANT);
        }

        if (ctx.RETAIN() != null) {
            gather.mix(VariableDeclaration.RETAIN);
        }
        return null;
    }

    @Override
    public Object visitFunction_block_declaration(
            IEC61131Parser.Function_block_declarationContext ctx) {
        FunctionBlockDeclaration ast = new FunctionBlockDeclaration();
        ast.setRuleContext(ctx);


        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));

        ast.setFunctionBlockName(ctx.identifier.getText());
        ast.setFunctionBody((StatementList) ctx.body.accept(this));
        //Utils.setPosition(ast, ctx.FUNCTION_BLOCK, ctx.END_FUNCTION_BLOCK);
        return ast;
    }

    @Override
    public Object visitInterface_declaration(IEC61131Parser.Interface_declarationContext ctx) {
        InterfaceDeclaration ast = new InterfaceDeclaration();
        ast.setRuleContext(ctx);
        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        ast.setName(ctx.identifier.getText());
        ast.setMethods((List<MethodDeclaration>) ctx.methods().accept(this));
        if (ctx.sp != null) {
            ((List<String>) ctx.sp.accept(this)).forEach(i -> ast.addExtends(i));
        }
        return ast;
    }

    @Override
    public Object visitClass_declaration(IEC61131Parser.Class_declarationContext ctx) {
        ClassDeclaration ast = new ClassDeclaration();
        ast.setRuleContext(ctx);
        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        ast.setFinal_(ctx.FINAL() != null);
        ast.setAbstract_(ctx.ABSTRACT() != null);
        ast.setName(ctx.identifier.getText());
        if (ctx.inherit != null) {
            ast.setParentClass(ctx.inherit.getText());
        }
        if (ctx.interfaces != null) {
            ast.addImplements((List<String>) ctx.interfaces.accept(this));
        }
        ast.setMethods((List<MethodDeclaration>) ctx.methods().accept(this));
        return ast;
    }

    @Override
    public List<MethodDeclaration> visitMethods(
            IEC61131Parser.MethodsContext ctx) {
        return ctx.method().stream()
                .map(a -> (MethodDeclaration) a.accept(this))
                .collect(Collectors.toList());
    }

    @Override
    public Object visitMethod(IEC61131Parser.MethodContext ctx) {
        MethodDeclaration ast = new MethodDeclaration();
        ast.setName(ctx.identifier.getText());
        if (ctx.access_specifier() != null) {
            ast.setAccessSpecifier(AccessSpecifier.valueOf(ctx.access_specifier().getText()));
        }
        if (ctx.returnET != null)
            ast.setReturnTypeName(ctx.returnET.getText());
        if (ctx.returnID != null)
            ast.setReturnTypeName(ctx.returnID.getText());

        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        ast.setStatements((StatementList) ctx.statement_list().accept(this));
        // ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitProgram_declaration(
            IEC61131Parser.Program_declarationContext ctx) {
        ProgramDeclaration ast = new ProgramDeclaration();
        ast.setRuleContext(ctx);
        ast.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        ast.setProgramName(ctx.identifier.getText());
        ast.setProgramBody((StatementList) ctx.body.accept(this));
        //Utils.setPosition(ast, ctx.PROGRAM(), ctx.END_PROGRAM());
        return ast;
    }

    @Override
    public Expression visitUnaryNegateExpr(
            IEC61131Parser.UnaryNegateExprContext ctx) {
        UnaryExpression ast = new UnaryExpression(Operators.NOT,
                (Expression) ctx.sub.accept(this));
        //Utils.setPosition(ast, ctx.NOT(), ctx.sub);
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitBinaryOrExpr(
            IEC61131Parser.BinaryOrExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);
    }

    @Override
    public Object visitBinaryCmpExpr(
            IEC61131Parser.BinaryCmpExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);
    }

    @Override
    public Object visitBinaryModDivExpr(
            IEC61131Parser.BinaryModDivExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);
    }

    @Override
    public Object visitParenExpr(
            IEC61131Parser.ParenExprContext ctx) {
        return ctx.expression().accept(this);
    }

    @Override
    public Object visitBinaryXORExpr(
            IEC61131Parser.BinaryXORExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);
    }

    @Override
    public Object visitUnaryMinusExpr(
            IEC61131Parser.UnaryMinusExprContext ctx) {
        UnaryExpression ast = new UnaryExpression(Operators.MINUS, (Expression) ctx.sub.accept(this));
        //Utils.setPosition(ast, ctx.NOT, ctx.sub.accept(this));
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitBinaryPowerExpr(
            IEC61131Parser.BinaryPowerExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);
    }

    @Override
    public Object visitBinaryMultExpr(
            IEC61131Parser.BinaryMultExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);

    }

    @Override
    public Object visitBinaryPlusMinusExpr(
            IEC61131Parser.BinaryPlusMinusExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);

    }

    @Override
    public Object visitBinaryEqExpr(
            IEC61131Parser.BinaryEqExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);

    }

    @Override
    public Object visitBinaryAndExpr(
            IEC61131Parser.BinaryAndExprContext ctx) {
        return binaryExpr(ctx.left, ctx.op, ctx.right).setRuleContext(ctx);

    }

    public Expression binaryExpr(IEC61131Parser.ExpressionContext left,
                                 Token op, IEC61131Parser.ExpressionContext right) {
        BinaryExpression ast = new BinaryExpression(
                (Expression) left.accept(this), (Expression) right.accept(this),
                op.getText());
        return ast;
    }

    @Override
    public Object visitFunctioncall(
            IEC61131Parser.FunctioncallContext ctx) {
        List<Expression> expr = allOf(ctx.expression());
        FunctionCall fc = new FunctionCall(ctx.id.getText(), expr);
        //        Utils.setPosition(ast, ctx.id, ctx.RPAREN);
        fc.setParameters(expr);
        return fc.setRuleContext(ctx);
    }

    @Override
    public Object visitStatement_list(
            IEC61131Parser.Statement_listContext ctx) {
        return new StatementList(allOf(ctx.statement()));
    }

    @Override
    public Object visitAssignment_statement(
            IEC61131Parser.Assignment_statementContext ctx) {
        AssignmentStatement ast = new AssignmentStatement(
                (Reference) ctx.a.accept(this),
                (Expression) ctx.expression().accept(this));
        ast.setReference(ctx.RASSIGN() != null);
        ast.setAssignmentAttempt(ctx.ASSIGN_ATTEMPT() != null);
        //setPosition(ast, ctx.ctx);
        return ast;
    }

    @Override
    public Object visitStatement(IEC61131Parser.StatementContext ctx) {
        return oneOf(ctx.assignment_statement(), ctx.if_statement(), ctx.exit_statement(),
                ctx.repeat_statement(), ctx.return_statement(), ctx.while_statement(),
                ctx.case_statement(), ctx.functionblockcall(), ctx.for_statement());
    }

    @Override
    public Object visitSymbolic_variable(IEC61131Parser.Symbolic_variableContext ctx) {
        //TODO REWORK
        SymbolicReference ast = new SymbolicReference();
        ast.setRuleContext(ctx);

        ast.setIdentifier(ctx.a.getText());
        ast.setSub(ctx.DOT() != null
                ? (SymbolicReference) ctx.other.accept(this)
                : null);

        if (ctx.subscript_list() != null) {
            ast.setSubscripts((ExpressionList) ctx.subscript_list().accept(this));
        }

        if (ctx.REF() != null) {
            ast.derefSubscript();
        }

        return ast;
    }

    @Override
    public ExpressionList visitSubscript_list(
            IEC61131Parser.Subscript_listContext ctx) {
        return new ExpressionList(allOf(ctx.expression()));
    }

    @Override
    public Object visitDirect_variable(
            IEC61131Parser.Direct_variableContext ctx) {
        DirectVariable ast = new DirectVariable(ctx.getText());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitReturn_statement(IEC61131Parser.Return_statementContext ctx) {
        ReturnStatement ast = new ReturnStatement();
        ast.setRuleContext(ctx);
        return ast;
//            Utils.setPosition(ast, ctx.RETURN);
    }

    @Override
    public Object visitFunctionblockcall(
            IEC61131Parser.FunctionblockcallContext ctx) {
        FunctionBlockCallStatement fbcs = new FunctionBlockCallStatement();
        fbcs.setFunctionBlockName(ctx.symbolic_variable().getText());
        ctx.param_assignment().stream().forEach(
                a ->
                        fbcs.getParameters().add(
                                (FunctionBlockCallStatement.Parameter)
                                        a.accept(this))
        );

        //setPosition
        return fbcs;
    }

    @Override
    public Object visitParam_assignment(
            IEC61131Parser.Param_assignmentContext ctx) {
        FunctionBlockCallStatement.Parameter p = new FunctionBlockCallStatement.Parameter();
        if (ctx.ARROW_RIGHT() != null)
            p.setOutput(true);

        p.setName(ctx.id.getText());
        p.setExpression((Expression) ctx.expression().accept(this));
        return p;
    }

    @Override
    public Object visitIf_statement(
            IEC61131Parser.If_statementContext ctx) {
        IfStatement ast = new IfStatement();
        for (int i = 0; i < ctx.cond.size(); i++) {
            ast.addGuardedCommand(
                    (Expression) ctx.cond.get(i).accept(this),
                    (StatementList) ctx.thenlist.get(i).accept(this));
        }
        if (ctx.ELSE() != null) {
            ast.setElseBranch((StatementList) ctx.elselist.accept(this));
        }
        //Utils.setPosition(ast, ctx.IF, ctx.END_IF);
        return ast;
    }

    @Override
    public Object visitCase_statement(
            IEC61131Parser.Case_statementContext ctx) {
        CaseStatement ast = new CaseStatement();
        ast.setRuleContext(ctx);

        ast.getCases().addAll(allOf(ctx.case_entry()));
        if (ctx.elselist != null)
            ast.setElseCase((StatementList) ctx.elselist.accept(this));

        ast.setExpression((Expression) ctx.cond.accept(this));
        return ast;
    }

    @Override
    public Object visitCase_entry(IEC61131Parser.Case_entryContext ctx) {
        CaseStatement.Case ast = new CaseStatement.Case();
        ast.getConditions().addAll(
                allOf(ctx.case_condition()));
        ast.setStatements((StatementList) ctx.statement_list().accept(this));
        return ast;
    }

    @Override
    public Object visitCase_condition(IEC61131Parser.Case_conditionContext ctx) {
        CaseCondition cc = null;
        if (ctx.IDENTIFIER() != null) {
            cc = new CaseCondition.Enumeration(
                    Literal.enumerate(ctx.IDENTIFIER().getSymbol()));
        }
        if (ctx.integer() != null) {
            cc = new CaseCondition.IntegerCondition((Literal)
                    ctx.integer().accept(this));
        }
        if (ctx.subrange() != null) {
            Range r = (Range) ctx.subrange().accept(this);
            cc = new CaseCondition.Range(r.getStart(), r.getStop());
        }
        if (ctx.cast() != null) {
            cc = new CaseCondition.Enumeration((Literal) ctx.cast().accept(this));
        }
        cc.setRuleContext(ctx);
        return cc;
    }


    @Override
    public Object visitFor_statement(IEC61131Parser.For_statementContext ctx) {
        ForStatement ast = new ForStatement();
        ast.setRuleContext(ctx);

        if (ctx.step != null) {
            ast.setStep((Expression) ctx.step.accept(this));
        }
        ast.setVariable(ctx.var.getText());
        ast.setStatements((StatementList) ctx.statement_list().accept(this));
        ast.setStop((Expression) ctx.endPosition.accept(this));
        ast.setStart((Expression) ctx.begin.accept(this));
        return ast;
    }

    @Override
    public Object visitWhile_statement(
            IEC61131Parser.While_statementContext ctx) {
        WhileStatement ast = new WhileStatement();
        ast.setRuleContext(ctx);

        ast.setCondition((Expression) ctx.expression().accept(this));
        ast.setStatements((StatementList) ctx.statement_list().accept(this));
        return ast;
    }

    @Override
    public Object visitRepeat_statement(
            IEC61131Parser.Repeat_statementContext ctx) {
        RepeatStatement ast = new RepeatStatement();
        ast.setCondition((Expression) ctx.expression().accept(this));
        ast.setStatements((StatementList) ctx.statement_list().accept(this));
        return ast;
    }

    @Override
    public Object visitExit_statement(IEC61131Parser.Exit_statementContext ctx) {
        ExitStatement ast = new ExitStatement();
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitStart_sfc(IEC61131Parser.Start_sfcContext ctx) {
        sfc = new SFCDeclaration();
        sfc.setBlockName(ctx.IDENTIFIER().getText());
        sfc.setActions(allOf(ctx.action_declaration()));
        sfc.setSteps(allOf(ctx.step_declaration()));
        sfc.setTransitions(allOf(ctx.goto_declaration()));
        return sfc;
    }

    @Override
    public Object visitGoto_declaration(IEC61131Parser.Goto_declarationContext ctx) {
        TransitionDeclaration t = new TransitionDeclaration();
        t.setFrom((List<String>) ctx.from.accept(this));
        t.setTo((List<String>) ctx.to.accept(this));
        t.setGuard((Expression) ctx.guard.accept(this));
        return t;
    }

    @Override
    public Object visitAction_declaration(IEC61131Parser.Action_declarationContext ctx) {
        FunctionBlockDeclaration fbd = new FunctionBlockDeclaration();
        fbd.setFunctionBlockName(ctx.IDENTIFIER().getText());
        fbd.setLocalScope((LocalScope) ctx.var_decls().accept(this));
        fbd.setFunctionBody((StatementList) ctx.statement_list().accept(this));
        return fbd;
    }

    @Override
    public Object visitStep_declaration(IEC61131Parser.Step_declarationContext ctx) {
        stepDeclaration = new StepDeclaration();
        stepDeclaration.setName(ctx.IDENTIFIER().getText());
        allOf(ctx.event());
        return stepDeclaration;
    }

    @Override
    public Object visitEvent(IEC61131Parser.EventContext ctx) {
        String type = ctx.type.getText();
        if (ctx.action != null) {
            stepDeclaration.addEvent(type, ctx.action.getText());
        } else {
            FunctionBlockDeclaration fbd = new FunctionBlockDeclaration();
            fbd.setFunctionBody((StatementList) ctx.body.accept(this));
            fbd.setFunctionBlockName(Utils.getRandomName());
            sfc.getActions().add(fbd);
            stepDeclaration.addEvent(type, fbd.getFunctionBlockName());
        }
        return null;
    }
}