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
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.sfclang.ast.*;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (23.06.17)
 */
public class IECParseTreeToAST extends IEC61131ParserBaseVisitor<Object> {
    private SFCNetwork network;
    private VariableBuilder gather;
    private SFCImplementation sfc;
    private SFCStep currentStep;
    private TopLevelScopeElement currentTopLevelScopeElement;

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
    public Object visitRef_null(IEC61131Parser.Ref_nullContext ctx) {
        Literal ast = Literal.ref_null(ctx.NULL().getSymbol());
        ast.setRuleContext(ctx);
        return ast;
    }

    @Override
    public Object visitReference_value(IEC61131Parser.Reference_valueContext ctx) {
        ReferenceValue ast = new ReferenceValue();
        ast.setRuleContext(ctx);
        ast.setReferenceTo((SymbolicReference) ctx.ref_to.accept(this));
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
        SimpleTypeDeclaration<Initialization> td = new SimpleTypeDeclaration<>();
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
                ctx.structure_declaration(), ctx.reference_specification(),
                ctx.data_type_name());

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

        /*if (ctx.basename != null) {
            ast.setBaseTypeName(ctx.basename.getText());
        }*/
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

        ctx.array_initial_elements().forEach(a -> ast.addAll((List<Initialization>) a.accept(this)));
        return ast;
    }

    @Override
    public Object visitArray_initial_elements(
            IEC61131Parser.Array_initial_elementsContext ctx) {
        List<Initialization> initializations = new ArrayList<>();
        int count = 1;
        if (ctx.integer() != null)
            count = Integer.parseInt(((Literal) ctx.integer().accept(this)).getTextValue());
        for (int i = 0; i < count; i++)
            initializations.add((Initialization) ctx.array_initial_element().accept(this));
        return initializations;
    }

    @Override
    public Object visitArray_initial_element(
            IEC61131Parser.Array_initial_elementContext ctx) {
        return oneOf(ctx.constant(), ctx.structure_initialization(), ctx.array_initialization());
    }

    @Override
    public Object visitStructure_declaration(
            IEC61131Parser.Structure_declarationContext ctx) {
        StructureTypeDeclaration ast = new StructureTypeDeclaration();
        Scope localScope = new Scope();
        gather = localScope.builder();
        Streams.forEachPair(ctx.ids.stream(), ctx.tds.stream(),
                (id, type) -> gather.identifiers(id.getText())
                        .type((TypeDeclaration) type.accept(this)).close());
        gather = null;
        ast.setFields(localScope.getVariables());
        return ast;
    }

    @Override
    public Object visitStructure_initialization(
            IEC61131Parser.Structure_initializationContext ctx) {
        // Includes class and FB initializations
        StructureInitialization ast = new StructureInitialization();
        ast.setRuleContext(ctx);
        for (int i = 0; i < ctx.IDENT.size(); i++)
            ast.addField(ctx.IDENT.get(i).getText(), (Initialization) ctx.init.get(i).accept(this));
        return ast;
    }

    @Override
    public Object visitReference_specification(IEC61131Parser.Reference_specificationContext ctx) {
        ReferenceSpecification ast = new ReferenceSpecification();
        ast.setRuleContext(ctx);
        ast.setRefTo((TypeDeclaration<Initialization>) ctx.type_declaration().accept(this));
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
        currentTopLevelScopeElement = ast;
        ast.setRuleContext(ctx);
        ast.setName(ctx.identifier.getText());
        ast.setScope((Scope) ctx.var_decls().accept(this));
        if (ctx.returnET != null) {
            ast.setReturnTypeName(ctx.returnET.getText());
        } else {
            ast.setReturnTypeName(ctx.returnID.getText());
        }
        ast.setName(ctx.identifier.getText());
        ast.setStBody((StatementList) ctx.funcBody().statement_list().accept(this));
        return ast;
    }

    @Override
    public Object visitGlobal_variable_list_declaration(IEC61131Parser.Global_variable_list_declarationContext ctx) {
        GlobalVariableListDeclaration gvl = new GlobalVariableListDeclaration();
        gather = gvl.getScope().builder();
        ctx.var_decl_inner().accept(this);
        //gather.mix(VariableDeclaration.GLOBAL);
        gvl.getScope().forEach(v -> v.setParent(gvl));
        gather = null;
        return gvl;
    }

    @Override
    public Object visitVar_decls(IEC61131Parser.Var_declsContext ctx) {
        Scope localScope = new Scope();
        gather = localScope.builder();
        ctx.var_decl().forEach(vd -> {
            vd.accept(this);
        });
        assert currentTopLevelScopeElement != null;
        for (VariableDeclaration variableDeclaration : localScope.getVariables().values())
            variableDeclaration.setParent(currentTopLevelScopeElement);
        gather = null;
        return localScope;
    }

    @Override
    public Object visitVar_decl(IEC61131Parser.Var_declContext ctx) {
        gather.clear();
        ctx.variable_keyword().accept(this);
        ctx.var_decl_inner().accept(this);
        return null;
    }

    @Override
    public Object visitVar_decl_inner(IEC61131Parser.Var_decl_innerContext ctx) {
        for (int i = 0; i < ctx.type_declaration().size(); i++) {
            gather.identifiers((List<String>) ctx.identifier_list(i).accept(this))
                    .type((TypeDeclaration) ctx.type_declaration(i).accept(this)).close();

        }
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

        // Access specifier
        if (ctx.access_specifier() != null) {
            gather.mix(VariableDeclaration.ACCESS_SPECIFIER_DICT.get(
                    AccessSpecifier.valueOf(ctx.access_specifier().getText())));
        }
        return null;
    }

    @Override
    public Object visitFunction_block_declaration(IEC61131Parser.Function_block_declarationContext ctx) {
        FunctionBlockDeclaration ast = new FunctionBlockDeclaration();
        currentTopLevelScopeElement = ast;
        ast.setRuleContext(ctx);
        ast.setScope((Scope) ctx.var_decls().accept(this));
        ast.setFinal_(ctx.FINAL() != null);
        ast.setAbstract_(ctx.ABSTRACT() != null);
        ast.setName(ctx.identifier.getText());
        if (ctx.inherit != null) {
            ast.setParentName(ctx.inherit.getText());
        }
        if (ctx.interfaces != null) {
            ((List<String>) ctx.interfaces.accept(this))
                    .forEach(i -> ast.getInterfaces().add(new IdentifierPlaceHolder<>(i)));
        }
        ast.setScope((Scope) ctx.var_decls().accept(this));
        ast.getMethods().addAll((List<MethodDeclaration>) ctx.methods().accept(this));

        ctx.action().forEach(act -> {
            ast.addAction((ActionDeclaration) act.accept(this));
        });

        if (ctx.body().statement_list() != null)
            ast.setStBody((StatementList) ctx.body().statement_list().accept(this));
        if (ctx.body().sfc() != null)
            ast.setSfcBody((SFCImplementation) ctx.body().sfc().accept(this));

        return ast;
    }

    @Override
    public Object visitInterface_declaration(IEC61131Parser.Interface_declarationContext ctx) {
        InterfaceDeclaration ast = new InterfaceDeclaration();
        ast.setRuleContext(ctx);
        currentTopLevelScopeElement = ast;
        ast.setScope((Scope) ctx.var_decls().accept(this));
        ast.setName(ctx.identifier.getText());
        ast.setMethods((List<MethodDeclaration>) ctx.methods().accept(this));
        if (ctx.sp != null) {
            ((List<String>) ctx.sp.accept(this))
                    .forEach(i -> new IdentifierPlaceHolder<>(i));
        }
        return ast;
    }

    @Override
    public Object visitClass_declaration(IEC61131Parser.Class_declarationContext ctx) {
        ClassDeclaration ast = new ClassDeclaration();
        ast.setRuleContext(ctx);
        currentTopLevelScopeElement = ast;
        ast.setScope((Scope) ctx.var_decls().accept(this));
        ast.setFinal_(ctx.FINAL() != null);
        ast.setAbstract_(ctx.ABSTRACT() != null);
        ast.setName(ctx.identifier.getText());
        if (ctx.inherit != null) {
            ast.setParent(ctx.inherit.getText());
        }
        if (ctx.interfaces != null) {
            ((List<String>) ctx.interfaces.accept(this)).forEach(ast::addExtendsOrImplements);
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
        //ast.setRuleContext(ctx);
        ast.setName(ctx.identifier.getText());
        ast.setParent((Classifier<?>) currentTopLevelScopeElement);
        if (ctx.access_specifier() != null) {
            ast.setAccessSpecifier(AccessSpecifier.valueOf(ctx.access_specifier().getText()));
        }
        ast.setFinal_(ctx.FINAL() != null);
        ast.setAbstract_(ctx.ABSTRACT() != null);
        ast.setOverride(ctx.OVERRIDE() != null);

        if (ctx.returnET != null) {
            ast.setReturnTypeName(ctx.returnET.getText());
        } else {
            if (ctx.returnID != null) {
                ast.setReturnTypeName(ctx.returnID.getText());
            } else {
                ast.setReturnTypeName("VOID");
            }
        }


        //currentTopLevelScopeElement = ast;
        ast.setScope((Scope) ctx.var_decls().accept(this));

        if (ctx.body().statement_list() != null)
            ast.setStBody((StatementList) ctx.body().statement_list().accept(this));

        //currentTopLevelScopeElement = ast.getParent();
        return ast;
    }

    @Override
    public Object visitProgram_declaration(
            IEC61131Parser.Program_declarationContext ctx) {
        ProgramDeclaration ast = new ProgramDeclaration();
        ast.setRuleContext(ctx);
        ast.setProgramName(ctx.identifier.getText());
        currentTopLevelScopeElement = ast;
        ast.setScope((Scope) ctx.var_decls().accept(this));

        if (ctx.body().statement_list() != null)
            ast.setStBody((StatementList) ctx.body().statement_list().accept(this));
        if (ctx.body().sfc() != null)
            ast.setSfcBody((SFCImplementation) ctx.body().sfc().accept(this));

        ctx.action().forEach(act -> {
            ast.addAction((ActionDeclaration) act.accept(this));
        });

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
    public Object visitInvocation(IEC61131Parser.InvocationContext ctx) {
        Invocation i = new Invocation();
        i.setCallee((SymbolicReference) ctx.id.accept(this));
        if (ctx.expression().isEmpty()) {
            // Using parameters
            i.addParameters(allOf(ctx.param_assignment()));
        } else {
            // Using expressions
            i.addExpressionParameters(allOf(ctx.expression()));
        }
        return i.setRuleContext(ctx);
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
                ctx.case_statement(), ctx.invocation_statement(),
                ctx.for_statement());
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

        ast.setDerefCount(ctx.deref.size());

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
    public Object visitInvocation_statement(IEC61131Parser.Invocation_statementContext ctx) {
        InvocationStatement is = new InvocationStatement();
        is.setInvocation((Invocation) ctx.invocation().accept(this));
        return is;
    }

    @Override
    public Object visitParam_assignment(
            IEC61131Parser.Param_assignmentContext ctx) {
        Invocation.Parameter p = new Invocation.Parameter();
        if (ctx.ARROW_RIGHT() != null) {
            p.setOutput(true);
            p.setExpression((Expression) ctx.v.accept(this));
        } else
            p.setExpression((Expression) ctx.expression().accept(this));
        if (ctx.id != null)
            p.setName(ctx.id.getText());
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

        if (ctx.by != null) {
            ast.setStep((Expression) ctx.by.accept(this));
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
    public Object visitSfc(IEC61131Parser.SfcContext ctx) {
        sfc = new SFCImplementation();
        ctx.sfc_network().forEach(nc -> {
            sfc.getNetworks().add(visitSfc_network(nc));
        });
        return sfc;
    }

    @Override
    public SFCNetwork visitSfc_network(IEC61131Parser.Sfc_networkContext ctx) {
        network = new SFCNetwork();
        SFCStep initStep = (SFCStep) visitInit_step(ctx.init_step());
        network.getSteps().add(initStep);

        for (IEC61131Parser.StepContext stepContext : ctx.step()) {
            SFCStep s = (SFCStep) visitStep(stepContext);
            network.getSteps().add(s);
        }

        ctx.action().forEach(a -> {
            sfc.getActions().add(visitAction(a));
        });

        ctx.transition().forEach(t -> {
            visitTransition(t);
        });

        return network;
    }

    @Override
    public ActionDeclaration visitAction(IEC61131Parser.ActionContext ctx) {
        ActionDeclaration action = new ActionDeclaration();
        action.setName(ctx.IDENTIFIER().getSymbol().getText());
        if (ctx.body().statement_list() != null) {
            action.setStBody((StatementList) ctx.body().statement_list().accept(this));
        }

        if (ctx.body().sfc() != null) {
            action.setSfcBody((SFCImplementation) ctx.body().sfc().accept(this));
        }
        return action;
    }

    @Override
    public SFCStep visitInit_step(IEC61131Parser.Init_stepContext ctx) {
        currentStep = new SFCStep();
        currentStep.setName(ctx.step_name.getText());
        currentStep.setInitial(true);
        visitActionAssociations(ctx.action_association());
        return currentStep;
    }

    private void visitActionAssociations(List<IEC61131Parser.Action_associationContext> seq) {
        seq.forEach(ctx -> visitAction_association(ctx));
    }

    @Override
    public Object visitAction_association(IEC61131Parser.Action_associationContext ctx) {
        // 'N' | 'R' | 'S' | 'P' | ( ( 'L' | 'D' | 'SD' | 'DS' | 'SL' ) ',' Action_Time );
        SFCActionQualifier qualifier = new SFCActionQualifier();
        if (null != ctx.actionQualifier().expression()) {
            Expression expr = (Expression) ctx.actionQualifier().expression().accept(this);
            qualifier.setTime(expr);
        }

        String q = ctx.actionQualifier().IDENTIFIER().getText();
        qualifier.setQualifier(SFCActionQualifier.Qualifier.NON_STORED);
        for (SFCActionQualifier.Qualifier qual : SFCActionQualifier.Qualifier.values()) {
            if (qual.symbol.equalsIgnoreCase(q)) qualifier.setQualifier(qual);
        }
        currentStep.addAction(qualifier, ctx.actionName.getText());
        return null;
    }

    @Override
    public SFCStep visitStep(IEC61131Parser.StepContext ctx) {
        SFCStep s = new SFCStep();
        currentStep.setName(ctx.step_name.getText());
        currentStep.setInitial(false);
        visitActionAssociations(ctx.action_association());
        return currentStep;
    }

    @Override
    public Object visitTransition(IEC61131Parser.TransitionContext ctx) {
        assert network != null;
        SFCTransition transition = new SFCTransition();
        transition.setRuleContext(ctx);

        if (ctx.name != null)
            transition.setName(ctx.name.getText());

        if (ctx.INTEGER_LITERAL() != null) {
            Utils.Splitted s = Utils.split(ctx.INTEGER_LITERAL().getText());
            int priority = s.number().intValue();
            transition.setPriority(priority);
        }

        Set<SFCStep> from = (Set<SFCStep>) visitSteps(ctx.from);
        Set<SFCStep> to = (Set<SFCStep>) visitSteps(ctx.to);
        transition.setTo(to);
        transition.setFrom(from);
        transition.setGuard((Expression) ctx.transitionCond().expression().accept(this));
        return transition;
    }

    @Override
    public Set<SFCStep> visitSteps(IEC61131Parser.StepsContext ctx) {
        return ctx.IDENTIFIER().stream()
                .map(n -> network.getStep(n.getSymbol().getText()))
                .filter(Optional::isPresent)
                .map(Optional::get)
                .collect(Collectors.toSet());
    }

}