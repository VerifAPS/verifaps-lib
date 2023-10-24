package edu.kit.iti.formal.automation.parser

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.DateAndTimeData
import edu.kit.iti.formal.automation.datatypes.values.DateData
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.datatypes.values.TimeofDayData
import edu.kit.iti.formal.automation.fbd.FbdBody
import edu.kit.iti.formal.automation.il.*
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.scope.TypeScope
import edu.kit.iti.formal.automation.sfclang.split
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.setAll
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import java.math.BigInteger
import java.util.*
import kotlin.collections.HashMap

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (23.06.17)
 */
class IECParseTreeToAST : IEC61131ParserBaseVisitor<Any>() {
    private lateinit var network: SFCNetwork
    private lateinit var gather: VariableBuilder
    private lateinit var sfc: SFCImplementation
    private lateinit var currentStep: SFCStep

    //private lateinit var currentTopLevelScopeElement: HasScope
    private var tscope = TypeScope.builtin()

    override fun visitStart(
            ctx: IEC61131Parser.StartContext): PouElements {
        val ast = PouElements()
        ast.ruleContext = ctx
        ctx.library_element_declaration().forEach { l ->
            val accept = l.accept(this) as? PouElement
            if (accept != null)
                ast.add(accept)
        }
        return ast
    }

    override fun visitLibrary_element_declaration(ctx: IEC61131Parser.Library_element_declarationContext): Any {
        val elemen = oneOf<Top>(
                ctx.class_declaration(), ctx.data_type_declaration(), ctx.function_block_declaration(),
                ctx.function_declaration(), ctx.global_variable_list_declaration(), ctx.interface_declaration(),
                ctx.namespace_declaration(), ctx.program_declaration())
        if (ctx.pragma() != null && elemen != null) {
            if (elemen is HasPragma) {
                val p = ctx.pragma().map { it.accept(this) as Pragma }
                elemen.pragmas.addAll(p)
            } else {
                throw RuntimeException("Pragma not supported ${elemen.nodeName} " +
                        "at line ${ctx.start.tokenSource.sourceName}:${ctx.start.line}.")
            }
        }
        return elemen!!
    }

    override fun visitNamespace_elements(ctx: IEC61131Parser.Namespace_elementsContext): Any {
        val elemen = oneOf<Any>(ctx.class_declaration(), ctx.data_type_declaration(), ctx.function_block_declaration(),
                ctx.function_declaration(), ctx.interface_declaration(),
                ctx.namespace_declaration())

        if (ctx.pragma() != null) {
            if (elemen is HasPragma) {
                val p = ctx.pragma().map { it.accept(this) as Pragma }
                elemen.pragmas.addAll(p)
            } else {
                throw RuntimeException("Pragma not supported at line ${ctx.start.line}.")
            }
        }
        return elemen!!
    }

    override fun visitPragma(ctx: IEC61131Parser.PragmaContext): Any {
        val rawParameters = HashMap<String, String>()
        var position: Int = 0;
        ctx.pragma_arg().forEach {
            val value = it.value.text.trim('\'', '"')
            if (it.ASSIGN() == null)
                rawParameters["#" + (position++)] = value
            else
                rawParameters[it.arg.text.trim('"', '\'')] = value
        }
        val p = makePragma(ctx.type.text, rawParameters)
                ?: throw IllegalArgumentException("Pragma ${ctx.type.text} in line ${ctx.type.line} not supported")
        return p
    }

    override fun visitCast(ctx: IEC61131Parser.CastContext): Literal {
        val (dt, _, v) = split(ctx.CAST_LITERAL().text)
        val ast = EnumLit(dt, v)
        //ast.originalToken = ctx.CAST_LITERAL().symbol
        ast.ruleContext = ctx
        return ast
    }

    override fun visitInteger(ctx: IEC61131Parser.IntegerContext): Any {
        val text = ctx.INTEGER_LITERAL().symbol
        val splitted = split(text.text)

        val dt = splitted.prefix
        val v = splitted.value
        val ordinal = splitted.ordinal ?: 10

        var int = BigInteger(v.replace("_", ""), ordinal)
        if (ctx.MINUS() != null)
            int *= -BigInteger.ONE
        val ast = IntegerLit(dt, int)
        try {
            //weigl: quick type for common integer type
            if (dt in tscope)
                ast.dataType.obj = tscope[dt] as AnyInt
        } catch (e: ClassCastException) {
        }
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBits(ctx: IEC61131Parser.BitsContext): Any {
        val text = ctx.BITS_LITERAL().symbol
        val splitted = split(text.text)
        val dt = splitted.prefix
        val v = splitted.value
        if (v.equals("false", true))
            return BooleanLit(false)
        if (v.equals("true", true))
            return BooleanLit(true)


        val ordinal = splitted.ordinal ?: 10
        val ast = BitLit(dt, v.toLong(ordinal))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitReal(ctx: IEC61131Parser.RealContext): Any {
        val (dt, _, v) = split(ctx.REAL_LITERAL().text)
        val ast = RealLit(dt, v.toBigDecimal())
        ast.ruleContext = ctx
        return ast
    }

    override fun visitString(ctx: IEC61131Parser.StringContext): Any {
        val ast = StringLit(
                if (ctx.STRING_LITERAL() != null) IECString.STRING
                else IECString.WSTRING,
                if (ctx.WSTRING_LITERAL() != null) ctx.text.trim('"')
                else ctx.text.trim('\''))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitTime(ctx: IEC61131Parser.TimeContext): Any {
        val ast = TimeLit(value = TimeData(ctx.text))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitTimeofday(ctx: IEC61131Parser.TimeofdayContext): Any {
        val ast = ToDLit(value = TimeofDayData.parse(ctx.TOD_LITERAL().text!!))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitDate(ctx: IEC61131Parser.DateContext): Any {
        val ast = DateLit(value = DateData.parse(ctx.DATE_LITERAL().text!!))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitDatetime(ctx: IEC61131Parser.DatetimeContext): Any {
        val ast = DateAndTimeLit(value = DateAndTimeData.parse(ctx.DATETIME().text))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitRef_null(ctx: IEC61131Parser.Ref_nullContext): Any {
        val ast = NullLit()
        ast.ruleContext = ctx
        return ast
    }

    override fun visitReference_value(ctx: IEC61131Parser.Reference_valueContext): Any {
        val ast = Invocation("ref")
        val p = InvocationParameter(ctx.ref_to.accept(this) as SymbolicReference)
        p.ruleContext = ctx.ref_to
        ast.addParameter(p)
        return ast
    }

    override fun visitData_type_declaration(
            ctx: IEC61131Parser.Data_type_declarationContext): Any {
        val ast = TypeDeclarations()
        ast.ruleContext = ctx
        for (i in 0 until ctx.type_declaration().size) {
            val t = ctx.type_declaration(i).accept(this) as TypeDeclaration
            ast.add(t)
            t.name = ctx.IDENTIFIER(i).text
        }
        //Utils.setPosition(ast, ctx.TYPE, ctx.END_TYPE);
        return ast
    }

    override fun visitData_type_name(
            ctx: IEC61131Parser.Data_type_nameContext): SimpleTypeDeclaration {
        val td = SimpleTypeDeclaration()
        td.ruleContext = ctx
        td.baseType.identifier = ctx.non_generic_type_name().text
        return td
    }

    private fun <T> allOf(ctx: List<ParserRuleContext>) =
            ctx.map { a -> a.accept(this) as T }
                    .toMutableList()

    private fun <T> oneOf(vararg children: ParserRuleContext?): T? {
        val fnn = children.find { it != null }
        if (fnn != null) {
            return fnn.accept(this) as T
        } else {
            return null
        }
        /*
        val call = { r: ParserRuleContext -> if (r != null) r.accept(this) as T else null }
        for (c in children) {
            val a = call(c)
            if (a != null)
                return a
        }
        return null*/
    }

    override fun visitType_declaration(
            ctx: IEC61131Parser.Type_declarationContext): Any {
        val init = (if (ctx.initializations() != null)
            ctx.initializations().accept(this) else null) as Initialization?

        if (ctx.array_specification() != null) {
            val t = visitArray_specification(ctx.array_specification())
            t.initialization = init as ArrayInitialization?
            return t
        } else if (ctx.enumerated_specification() != null) {
            val t = visitEnumerated_specification(ctx.enumerated_specification())
            t.initialization = init as IdentifierInitializer?
            return t
        } else if (ctx.string_type_declaration() != null) {
            val t = visitString_type_declaration(ctx.string_type_declaration())
            t.initialization = init as Literal?
            return t
        } else if (ctx.subrange_spec_init() != null) {
            val t = visitSubrange_spec_init(ctx.subrange_spec_init())
            t.initialization = init as? IntegerLit
            return t
        } else if (ctx.structure_declaration() != null) {
            val t = visitStructure_declaration(ctx.structure_declaration())
            t.initialization = init as StructureInitialization?
            return t
        } else if (ctx.reference_specification() != null) {
            val t = visitReference_specification(ctx.reference_specification())
            t.initialization = init as Literal?
            return t
        } else
        //if(ctx.data_type_name() != null)
        {
            val t = visitData_type_name(ctx.data_type_name())
            t.setInit(init)
            return t
        }
    }

    override fun visitInitializations_identifier(
            ctx: IEC61131Parser.Initializations_identifierContext) = IdentifierInitializer(null, ctx.IDENTIFIER().text)

    override fun visitSubrange_spec_init(
            ctx: IEC61131Parser.Subrange_spec_initContext): SubRangeTypeDeclaration {
        val ast = SubRangeTypeDeclaration()
        ast.ruleContext = ctx

        ast.baseType.identifier = ctx.integer_type_name().text
        ast.range = ctx.subrange().accept(this) as Range
        //Utils.setPosition(ast, ctx.integer_type_name.ctx, ctx.RPAREN);
        return ast
    }

    override fun visitSubrange(ctx: IEC61131Parser.SubrangeContext) =
            Range(ctx.c.accept(this) as IntegerLit, ctx.d.accept(this) as IntegerLit)

    override fun visitEnumerated_specification(
            ctx: IEC61131Parser.Enumerated_specificationContext): EnumerationTypeDeclaration {
        val ast = EnumerationTypeDeclaration()
        ast.ruleContext = ctx


        for (i in ctx.value.indices) {
            ast.addValue(ctx.value[i])
            if (ctx.integer(i) != null) {
                ast.setInt(ctx.integer(i).accept(this) as IntegerLit)
            }
        }

        /*if (ctx.basename != null) {
            ast.setBaseTypeName(ctx.basename.getText());
        }*/
        return ast
    }

    override fun visitArray_specification(
            ctx: IEC61131Parser.Array_specificationContext): ArrayTypeDeclaration {
        val ast = ArrayTypeDeclaration(
                type = if (ctx.non_generic_type_name() != null)
                    SimpleTypeDeclaration(ctx.non_generic_type_name()!!.text)
                else
                    ctx.string_type_declaration().accept(this) as StringTypeDeclaration
        )

        for (src in ctx.ranges)
            ast.addSubRange(src.accept(this) as Range)
        return ast
    }

    override fun visitArray_initialization(
            ctx: IEC61131Parser.Array_initializationContext): Any {
        val ast = ArrayInitialization()
        ast.ruleContext = ctx

        ctx.array_initial_elements().forEach { a ->
            val inits = a.accept(this) as List<Initialization>
            ast.initValues.addAll(inits)
        }
        return ast
    }

    override fun visitArray_initial_elements(
            ctx: IEC61131Parser.Array_initial_elementsContext): Any {
        val initializations = ArrayList<Initialization>()
        var count = 1
        if (ctx.integer() != null) {
            val lit = ctx.integer().accept(this) as IntegerLit
            count = lit.value.toInt()
        }
        for (i in 0 until count)
            initializations.add(ctx.array_initial_element().accept(this) as Initialization)
        return initializations
    }

    override fun visitArray_initial_element(
            ctx: IEC61131Parser.Array_initial_elementContext): Any? {
        return oneOf<Any>(ctx.constant(), ctx.structure_initialization(), ctx.array_initialization())
    }

    override fun visitStructure_declaration(
            ctx: IEC61131Parser.Structure_declarationContext): StructureTypeDeclaration {
        val ast = StructureTypeDeclaration()
        val localScope = Scope()
        gather = localScope.builder()
        ctx.ids.zip(ctx.tds).forEach { (id, type) ->
            gather.identifiers(id.IDENTIFIER().symbol).type(type.accept(this) as TypeDeclaration).close()
        }
        //gather = null
        ast.fields = localScope.variables
        return ast
    }

    override fun visitStructure_initialization(
            ctx: IEC61131Parser.Structure_initializationContext): Any {
        // Includes class and FB initializations
        val ast = StructureInitialization()
        ast.ruleContext = ctx
        for (i in ctx.IDENT.indices)
            ast.addField(ctx.IDENT[i].text, ctx.init[i].accept(this) as Initialization)
        return ast
    }

    override fun visitReference_specification(ctx: IEC61131Parser.Reference_specificationContext): ReferenceTypeDeclaration {
        val ast = ReferenceTypeDeclaration()
        ast.ruleContext = ctx
        ast.refTo = ctx.data_type_name().accept(this) as SimpleTypeDeclaration
        return ast
    }

    override fun visitString_type_declaration(
            ctx: IEC61131Parser.String_type_declarationContext): StringTypeDeclaration {
        val ast = StringTypeDeclaration()
        ast.ruleContext = ctx

        ast.baseType.identifier = ctx.baseType.text
        if (ctx.integer() != null) {
            ast.size = ctx.integer().accept(this) as Literal
        }
        return ast
    }

    override fun visitIdentifier_list(
            ctx: IEC61131Parser.Identifier_listContext): List<String> {
        return ctx.names.map { it.text }
    }

    override fun visitFunction_declaration(
            ctx: IEC61131Parser.Function_declarationContext): Any {
        val ast = FunctionDeclaration()
        //currentTopLevelScopeElement = ast
        ast.ruleContext = ctx
        ast.name = ctx.identifier.text
        ast.scope = ctx.var_decls().accept(this) as Scope
        if (ctx.returnET != null) {
            ast.returnType.identifier = ctx.returnET.text
        } else {
            ast.returnType.identifier = ctx.returnID.text
        }
        ast.name = ctx.identifier.text
        ast.stBody = ctx.funcBody().statement_list().accept(this) as StatementList
        return ast
    }

    override fun visitGlobal_variable_list_declaration(ctx: IEC61131Parser.Global_variable_list_declarationContext): Any {
        val gvl = GlobalVariableListDeclaration()
        gather = gvl.scope.builder()
        gather.push(VariableDeclaration.GLOBAL)
        ctx.var_decl_inner().accept(this)

        //gvl.scope.forEach { v -> v.parent = gvl }
        //gather = null
        return gvl
    }

    override fun visitVar_decls(ctx: IEC61131Parser.Var_declsContext): Any {
        val localScope = Scope()
        gather = localScope.builder()
        ctx.var_decl().forEach { vd -> vd.accept(this) }
        return localScope
    }

    override fun visitVar_decl(ctx: IEC61131Parser.Var_declContext): Any? {
        gather.clear()
        val p = ctx.pragma().map { it.accept(this) as Pragma }
        gather.pushPragma(p)
        ctx.variable_keyword().accept(this)
        ctx.var_decl_inner().accept(this)
        gather.popPragma()
        return null
    }


    fun <T> List<ParserRuleContext>.map(): MutableList<T> = this.map { it -> it.accept(this@IECParseTreeToAST) as T }.toMutableList()

    override fun visitBlock_statement(ctx: IEC61131Parser.Block_statementContext): BlockStatement {
        val bs = BlockStatement()
        val statementList = ctx.statement_list().accept(this) as StatementList
        bs.statements = statementList
        bs.name = ctx.id.text
        bs.state = ctx.state?.accept(this) as MutableList<SymbolicReference>? ?: arrayListOf()
        bs.input = ctx.input?.accept(this) as MutableList<SymbolicReference>? ?: arrayListOf()
        bs.output = ctx.output?.accept(this) as MutableList<SymbolicReference>? ?: arrayListOf()
        bs.ruleContext = ctx
        return bs
    }

    override fun visitRef_list(ctx: IEC61131Parser.Ref_listContext): Any {
        return ctx.symbolic_variable().map { it.accept(this) }
    }

    override fun visitVar_decl_inner(ctx: IEC61131Parser.Var_decl_innerContext): Any? {
        val p: List<Pragma> = ctx.pragma().map()
        for (i in 0 until ctx.type_declaration().size) {
            val seq = ctx.identifier_list(i).names.map { it }

            gather
                    .pushPragma(p)
                    .identifiers(seq)
                    .type(ctx.type_declaration(i).accept(this) as TypeDeclaration)
                    .close()
                    .popPragma()
        }
        return null
    }

    override fun visitVariable_keyword(ctx: IEC61131Parser.Variable_keywordContext): Any? {
        if (ctx.VAR() != null) {
            gather.push(VariableDeclaration.LOCAL)
        }
        if (ctx.VAR_INPUT() != null) {
            gather.push(VariableDeclaration.INPUT)
        }
        if (ctx.VAR_OUTPUT() != null) {
            gather.push(VariableDeclaration.OUTPUT)
        }
        if (ctx.VAR_IN_OUT() != null) {
            gather.push(VariableDeclaration.INOUT)
        }
        if (ctx.VAR_EXTERNAL() != null) {
            gather.push(VariableDeclaration.EXTERNAL)
        }
        if (ctx.VAR_GLOBAL() != null) {
            gather.push(VariableDeclaration.GLOBAL)
        }

        if (ctx.CONSTANT() != null) {
            gather.mix(VariableDeclaration.CONSTANT)
        }

        if (ctx.RETAIN() != null) {
            gather.mix(VariableDeclaration.RETAIN)
        }

        // Access specifier
        if (ctx.access_specifier() != null) {
            val accessSpecifier = AccessSpecifier.valueOf(ctx.access_specifier().text)
            gather.mix(accessSpecifier.flag)
        }
        return null
    }

    override fun visitFunction_block_declaration(ctx: IEC61131Parser.Function_block_declarationContext): Any {
        val ast = FunctionBlockDeclaration()
        //currentTopLevelScopeElement = ast
        ast.ruleContext = ctx
        ast.scope = ctx.var_decls().accept(this) as Scope
        ast.isFinal = ctx.FINAL() != null
        ast.isAbstract = ctx.ABSTRACT() != null
        ast.name = ctx.identifier.text
        if (ctx.inherit != null) {
            ast.setParentName(ctx.inherit.text)
        }
        if (ctx.interfaces != null) {
            (ctx.interfaces.accept(this) as List<String>)
                    .forEach { i -> ast.interfaces.add(RefTo(i)) }
        }
        ast.scope = ctx.var_decls().accept(this) as Scope
        ast.methods.addAll(ctx.methods().accept(this) as List<MethodDeclaration>)

        ctx.action().forEach { act ->
            ast.addAction(act.accept(this) as ActionDeclaration)
        }

        if (ctx.body().stBody() != null)
            ast.stBody = ctx.body().stBody().accept(this) as StatementList
        if (ctx.body().sfc() != null)
            ast.sfcBody = ctx.body().sfc().accept(this) as SFCImplementation
        if (ctx.body().ilBody() != null)
            ast.ilBody = ctx.body().ilBody().accept(this) as IlBody
        if (ctx.body().fbBody() != null)
            ast.fbBody = ctx.body().fbBody().accept(this) as FbdBody
        return ast
    }

    override fun visitInterface_declaration(ctx: IEC61131Parser.Interface_declarationContext): Any {
        val ast = InterfaceDeclaration()
        ast.ruleContext = ctx
        //ast.scope = ctx.var_decls().accept(this) as Scope
        ast.name = ctx.identifier.text
        ast.methods.setAll(ctx.methods().accept(this) as List<MethodDeclaration>)

        if (ctx.sp != null) {
            (ctx.sp.accept(this) as List<String>).forEach { i -> ast.interfaces.add(RefTo(i)) }
        }
        return ast
    }

    override fun visitClass_declaration(ctx: IEC61131Parser.Class_declarationContext): Any {
        val ast = ClassDeclaration()
        ast.ruleContext = ctx
        //currentTopLevelScopeElement = ast
        ast.scope = ctx.var_decls().accept(this) as Scope
        ast.isFinal = ctx.FINAL() != null
        ast.isAbstract = ctx.ABSTRACT() != null
        ast.name = ctx.identifier.text
        if (ctx.inherit != null) {
            ast.parent.identifier = ctx.inherit.text
        }
        if (ctx.interfaces != null) {
            (ctx.interfaces.accept(this) as List<String>)
                    .forEach { ast.interfaces.add(it) }
        }
        ast.methods.setAll(ctx.methods().accept(this) as List<MethodDeclaration>)
        return ast
    }

    override fun visitMethods(
            ctx: IEC61131Parser.MethodsContext): List<MethodDeclaration> {
        return ctx.method().map { a -> a.accept(this) as MethodDeclaration }
    }

    override fun visitMethod(ctx: IEC61131Parser.MethodContext): Any {
        val ast = MethodDeclaration()
        //ast.ruleContext = (ctx);
        ast.name = ctx.identifier.text
        //ast.parent = currentTopLevelScopeElement as Classifier<*>?
        if (ctx.access_specifier() != null) {
            ast.accessSpecifier = AccessSpecifier.valueOf(ctx.access_specifier().text)
        }
        ast.isFinal = ctx.FINAL() != null
        ast.isAbstract = ctx.ABSTRACT() != null
        ast.isOverride = ctx.OVERRIDE() != null

        if (ctx.returnET != null) {
            ast.returnType.identifier = ctx.returnET.text
        } else {
            if (ctx.returnID != null) {
                ast.returnType.identifier = ctx.returnID.text
            } else {
                ast.returnType.identifier = "VOID"
            }
        }


        //currentTopLevelScopeElement = ast;
        ast.scope = ctx.var_decls().accept(this) as Scope

        if (ctx.body().stBody() != null)
            ast.stBody = ctx.body().stBody().accept(this) as StatementList

        //currentTopLevelScopeElement = ast.getParent();
        return ast
    }

    override fun visitProgram_declaration(
            ctx: IEC61131Parser.Program_declarationContext): Any {
        val ast = ProgramDeclaration()
        ast.ruleContext = ctx
        ast.name = ctx.identifier.text
        //currentTopLevelScopeElement = ast
        ast.scope = ctx.var_decls().accept(this) as Scope

        if (ctx.body().stBody() != null)
            ast.stBody = ctx.body().stBody().accept(this) as StatementList
        if (ctx.body().sfc() != null)
            ast.sfcBody = ctx.body().sfc().accept(this) as SFCImplementation
        if (ctx.body().ilBody() != null)
            ast.ilBody = ctx.body().ilBody().accept(this) as IlBody
        if (ctx.body().fbBody() != null)
            ast.fbBody = ctx.body().fbBody().accept(this) as FbdBody

        ctx.action().forEach { act -> ast.addAction(act.accept(this) as ActionDeclaration) }

        return ast
    }

    override fun visitUnaryNegateExpr(
            ctx: IEC61131Parser.UnaryNegateExprContext): Expression {
        val ast = UnaryExpression(Operators.NOT,
                ctx.sub.accept(this) as Expression)
        //Utils.setPosition(ast, ctx.NOT(), ctx.sub);
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBinaryOrExpr(
            ctx: IEC61131Parser.BinaryOrExprContext): Any {
        val binaryExpr = binaryExpr(ctx.left, ctx.op, ctx.right)
        binaryExpr.ruleContext = (ctx)
        return binaryExpr
    }

    override fun visitBinaryCmpExpr(
            ctx: IEC61131Parser.BinaryCmpExprContext): Any {
        val expr = binaryExpr(ctx.left, ctx.op, ctx.right)
        expr.ruleContext = (ctx)
        return expr
    }

    override fun visitBinaryModDivExpr(
            ctx: IEC61131Parser.BinaryModDivExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitParenExpr(
            ctx: IEC61131Parser.ParenExprContext): Any {
        return ctx.expression().accept(this)
    }

    override fun visitBinaryXORExpr(
            ctx: IEC61131Parser.BinaryXORExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitUnaryMinusExpr(
            ctx: IEC61131Parser.UnaryMinusExprContext): Any {
        val ast = UnaryExpression(Operators.MINUS, ctx.sub.accept(this) as Expression)
        //Utils.setPosition(ast, ctx.NOT, ctx.sub.accept(this));
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBinaryPowerExpr(
            ctx: IEC61131Parser.BinaryPowerExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryMultExpr(
            ctx: IEC61131Parser.BinaryMultExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryPlusMinusExpr(
            ctx: IEC61131Parser.BinaryPlusMinusExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryEqExpr(
            ctx: IEC61131Parser.BinaryEqExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryAndExpr(
            ctx: IEC61131Parser.BinaryAndExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    fun binaryExpr(left: IEC61131Parser.ExpressionContext,
                   op: Token, right: IEC61131Parser.ExpressionContext): Expression {
        val binOp = Operators.lookup(op.text) as BinaryOperator
        return BinaryExpression(
                left.accept(this) as Expression,
                binOp,
                right.accept(this) as Expression)
    }

    override fun visitInvocation(ctx: IEC61131Parser.InvocationContext): Any {
        val i = Invocation()
        i.callee = ctx.id.accept(this) as SymbolicReference
        if (ctx.expression().isEmpty()) {
            // Using parameters
            i.addParameters(allOf(ctx.param_assignment()))
        } else {
            // Using expressions
            i.addExpressionParameters(allOf(ctx.expression()))
        }
        i.ruleContext = (ctx)
        return i
    }


    override fun visitStatement_list(
            ctx: IEC61131Parser.Statement_listContext): Any {
        return StatementList(allOf(ctx.statement()))
    }


    override fun visitAssignment_statement(
            ctx: IEC61131Parser.Assignment_statementContext): Any {
        val ast = AssignmentStatement(
                ctx.a.accept(this) as SymbolicReference,
                ctx.expression().accept(this) as Expression)
        ast.reference = ctx.RASSIGN() != null
        ast.isAssignmentAttempt = ctx.ASSIGN_ATTEMPT() != null
        ast.ruleContext = ctx
        return ast
    }

    override fun visitStatement(ctx: IEC61131Parser.StatementContext): Any? {
        val statement = oneOf<Any>(ctx.assignment_statement(), ctx.if_statement(), ctx.exit_statement(),
                ctx.repeat_statement(), ctx.return_statement(), ctx.while_statement(),
                ctx.case_statement(), ctx.invocation_statement(), ctx.block_statement(),
                ctx.jump_statement(), ctx.for_statement(), ctx.special_statement()) as Statement
        val p = ctx.pragma().map { it.accept(this) as Pragma }
        if (p.isNullOrEmpty()) statement.pragmas += p
        return statement
    }


    override fun visitJump_statement(ctx: IEC61131Parser.Jump_statementContext) =
            JumpStatement(ctx.id.text)

    override fun visitLabel_statement(ctx: IEC61131Parser.Label_statementContext) =
            LabelStatement(ctx.id.text)


    override fun visitSymbolic_variable(ctx: IEC61131Parser.Symbolic_variableContext): Any {
        //TODO REWORK
        val ast = SymbolicReference()
        ast.ruleContext = ctx

        ast.identifier = ctx.a.text.trim('`')
        ast.sub = if (ctx.DOT() != null)
            ctx.other.accept(this) as SymbolicReference
        else
            null

        if (ctx.subscript_list() != null) {
            ast.subscripts = ctx.subscript_list().accept(this) as ExpressionList
        }

        ast.derefCount = ctx.deref.size

        return ast
    }

    override fun visitSubscript_list(
            ctx: IEC61131Parser.Subscript_listContext): ExpressionList {
        return ExpressionList(allOf<Expression>(ctx.expression()))
    }

    override fun visitDirect_variable(
            ctx: IEC61131Parser.Direct_variableContext): Any {
        val ast = DirectVariable(ctx.text)
        ast.ruleContext = ctx
        return ast
    }

    override fun visitReturn_statement(ctx: IEC61131Parser.Return_statementContext): Any {
        val ast = ReturnStatement()
        ast.ruleContext = ctx
        return ast
        //            Utils.setPosition(ast, ctx.RETURN);
    }

    override fun visitInvocation_statement(ctx: IEC61131Parser.Invocation_statementContext): Any {
        val call = InvocationStatement()
        val o = ctx.invocation().accept(this) as Invocation
        call.callee = o.callee
        call.parameters = o.parameters
        call.ruleContext = ctx
        return call
    }

    override fun visitParam_assignment(
            ctx: IEC61131Parser.Param_assignmentContext): Any {
        val p = InvocationParameter()
        p.ruleContext = ctx
        if (ctx.ARROW_RIGHT() != null) {
            p.isOutput = true
            p.expression = ctx.v.accept(this) as Expression
        } else
            p.expression = ctx.expression().accept(this) as Expression
        if (ctx.id != null)
            p.name = ctx.id.text
        return p
    }

    override fun visitIf_statement(
            ctx: IEC61131Parser.If_statementContext): Any {
        val ast = IfStatement()
        ast.ruleContext = ctx
        for (i in ctx.cond.indices) {
            val c = ctx.cond[i].accept(this) as Expression
            val b = ctx.thenlist[i].accept(this) as StatementList
            val gs = GuardedStatement(c, b)
            gs.ruleContext = ctx.cond[i]
            ast.addGuardedCommand(gs)
        }
        if (ctx.ELSE() != null) {
            ast.elseBranch = ctx.elselist.accept(this) as StatementList
        }
        return ast
    }

    override fun visitCase_statement(
            ctx: IEC61131Parser.Case_statementContext): Any {
        val ast = CaseStatement()
        ast.ruleContext = ctx

        ast.cases.addAll(allOf<Case>(ctx.case_entry()))
        if (ctx.elselist != null)
            ast.elseCase = ctx.elselist.accept(this) as StatementList

        ast.expression = ctx.cond.accept(this) as Expression
        return ast
    }

    override fun visitCase_entry(ctx: IEC61131Parser.Case_entryContext): Any {
        val ast = Case()
        ast.ruleContext = ctx
        ast.conditions.addAll(allOf(ctx.case_condition()))
        ast.statements = ctx.statement_list().accept(this) as StatementList
        return ast
    }

    override fun visitCase_condition(ctx: IEC61131Parser.Case_conditionContext): Any {
        var cc: CaseCondition? = null
        if (ctx.IDENTIFIER() != null) {
            cc = CaseCondition.Enumeration(EnumLit(null, ctx.IDENTIFIER().text))
        }
        if (ctx.integer() != null) {
            cc = CaseCondition.IntegerCondition(ctx.integer().accept(this) as IntegerLit)
        }
        if (ctx.subrange() != null) {
            val r = ctx.subrange().accept(this) as Range
            cc = CaseCondition.Range(Range(r.start, r.stop))
        }
        if (ctx.cast() != null) {
            cc = CaseCondition.Enumeration(ctx.cast().accept(this) as EnumLit)
        }
        cc!!.ruleContext = ctx
        return cc
    }

    override fun visitFor_statement(ctx: IEC61131Parser.For_statementContext): Any {
        val ast = ForStatement()
        ast.ruleContext = ctx

        if (ctx.by != null) {
            ast.step = ctx.by.accept(this) as Expression
        }
        ast.variable = ctx.`var`.text
        ast.statements = ctx.statement_list().accept(this) as StatementList
        ast.stop = ctx.endPosition.accept(this) as Expression
        ast.start = ctx.begin.accept(this) as Expression
        return ast
    }

    override fun visitWhile_statement(
            ctx: IEC61131Parser.While_statementContext): Any {
        val ast = WhileStatement()
        ast.ruleContext = ctx

        ast.condition = ctx.expression().accept(this) as Expression
        ast.statements = ctx.statement_list().accept(this) as StatementList
        return ast
    }

    override fun visitRepeat_statement(
            ctx: IEC61131Parser.Repeat_statementContext): Any {
        val ast = RepeatStatement()
        ast.condition = ctx.expression().accept(this) as Expression
        ast.statements = ctx.statement_list().accept(this) as StatementList
        return ast
    }

    override fun visitExit_statement(ctx: IEC61131Parser.Exit_statementContext): Any {
        val ast = ExitStatement()
        ast.ruleContext = ctx
        return ast
    }

    override fun visitSpecial_statement(ctx: IEC61131Parser.Special_statementContext): SpecialStatement {
        val exprs = ctx.expression()
                .map { it.accept(this) as Expression }
                .toMutableList()
        val id = ctx.id?.text
        val s = when (val name = ctx.type.text) {
            "assert" -> SpecialStatement.Assert(exprs, id)
            "assume" -> SpecialStatement.Assume(exprs, id)
            "havoc" -> SpecialStatement.Havoc(exprs.map { it as SymbolicReference }.toMutableList(), id)
            else -> error("Special statement of name $name unknown/unsupported.")
        }
        s.ruleContext = ctx
        return s
    }

    //region sfc
    override fun visitSfc(ctx: IEC61131Parser.SfcContext): Any {
        sfc = SFCImplementation()
        ctx.sfc_network().forEach { nc -> sfc.networks.add(visitSfc_network(nc)) }
        return sfc
    }

    override fun visitSfc_network(ctx: IEC61131Parser.Sfc_networkContext): SFCNetwork {
        network = SFCNetwork()
        network.steps.add(visitInit_step(ctx.init_step()))
        network.ruleContext = ctx

        for (stepContext in ctx.step()) {
            network.steps.add(visitStep(stepContext))
        }

        //ctx.action().forEach { a -> sfc!!.actions.add(visitAction(a)) }

        ctx.transition().forEach { t -> visitTransition(t) }

        return network
    }

    override fun visitAction(ctx: IEC61131Parser.ActionContext): ActionDeclaration {
        val action = ActionDeclaration()
        action.name = ctx.IDENTIFIER().symbol.text
        if (ctx.body().stBody() != null)
            action.stBody = ctx.body().stBody().accept(this) as StatementList
        if (ctx.body().sfc() != null)
            action.sfcBody = ctx.body().sfc().accept(this) as SFCImplementation
        if (ctx.body().ilBody() != null)
            action.ilBody = ctx.body().ilBody().accept(this) as IlBody
        if (ctx.body().fbBody() != null)
            action.fbBody = ctx.body().fbBody().accept(this) as FbdBody
        action.ruleContext = ctx
        return action
    }

    override fun visitStBody(ctx: IEC61131Parser.StBodyContext): Any {
        val statements = StatementList()
        if (ctx.startlbl != null)
            statements.add(ctx.startlbl.accept())
        statements.addAll(ctx.startstmts.accept());

        for (i in 0 until ctx.lbls.size) {
            statements.add(ctx.lbls[i].accept())
            statements.addAll(ctx.stmts[i].accept())
        }
        return statements
    }

    inline fun <T> ParserRuleContext?.accept(): T = this?.accept(this@IECParseTreeToAST) as T


    override fun visitInit_step(ctx: IEC61131Parser.Init_stepContext): SFCStep {
        currentStep = SFCStep()
        currentStep.name = ctx.step_name.text
        currentStep.isInitial = true
        visitActionAssociations(ctx.action_association())
        currentStep.ruleContext = ctx
        return currentStep
    }

    private fun visitActionAssociations(seq: List<IEC61131Parser.Action_associationContext>) {
        seq.forEach { ctx -> visitAction_association(ctx) }
    }

    override fun visitAction_association(ctx: IEC61131Parser.Action_associationContext): Any? {
        // 'N' | 'R' | 'S' | 'P' | ( ( 'L' | 'D' | 'SD' | 'DS' | 'SL' ) ',' Action_Time );
        val qualifier = SFCActionQualifier()
        if (null != ctx.actionQualifier().expression()) {
            val expr = ctx.actionQualifier().expression().accept(this) as Expression
            qualifier.time = expr
        }

        val q = ctx.actionQualifier().IDENTIFIER().text
        qualifier.qualifier = SFCActionQualifier.Qualifier.NON_STORED
        for (qual in SFCActionQualifier.Qualifier.entries) {
            if (qual.symbol.equals(q, ignoreCase = true)) qualifier.qualifier = qual
        }
        currentStep.addAction(qualifier, ctx.actionName.text)
        return null
    }

    override fun visitStep(ctx: IEC61131Parser.StepContext): SFCStep {
        currentStep = SFCStep()
        currentStep.ruleContext = ctx
        currentStep.name = ctx.step_name.text
        currentStep.isInitial = false
        visitActionAssociations(ctx.action_association())
        currentStep.ruleContext = ctx
        return currentStep
    }

    override fun visitTransition(ctx: IEC61131Parser.TransitionContext): Any {
        val transition = SFCTransition()
        transition.ruleContext = ctx

        if (ctx.id != null)
            transition.name = ctx.id.text

        if (ctx.INTEGER_LITERAL() != null) {
            val s = split(ctx.INTEGER_LITERAL().text)
            val priority = s.number().toInt()
            transition.priority = priority
        }

        transition.to = visitSteps(ctx.to)
        transition.from = visitSteps(ctx.from)
        transition.guard = ctx.transitionCond().expression().accept(this) as Expression

        transition.from.forEach { it.outgoing.add(transition) }
        transition.to.forEach { it.incoming.add(transition) }

        return transition
    }

    override fun visitSteps(ctx: IEC61131Parser.StepsContext): MutableSet<SFCStep> {
        return ctx.IDENTIFIER()
                .map { n -> network.getStep(n.symbol.text) }
                .filter { it.isPresent() }
                .map { it.get() }
                .toHashSet()
    }
    //endregion

    //region il
    override fun visitIlBody(ctx: IEC61131Parser.IlBodyContext): IlBody {
        val body = IlBody()
        ctx.ilInstruction().map { it.accept(this) }.forEach { body.add(it as IlInstr) }
        return body
    }

    override fun visitIlInstruction(ctx: IEC61131Parser.IlInstructionContext): IlInstr {
        val instr: IlInstr = ctx.ilInstr().accept(this) as IlInstr
        if (ctx.COLON() != null) {
            instr.labelled = ctx.IDENTIFIER()?.text
        }
        instr.ruleContext = ctx
        return instr
    }

    override fun visitIlInstr(ctx: IEC61131Parser.IlInstrContext) =
            oneOf<IlInstr>(ctx.ilCall(), ctx.ilExpr(), ctx.ilFormalFunctionCall(), ctx.ilJump(), ctx.ilSimple(),
                    ctx.ilFunctionCall())!!


    override fun visitIlSInstr(ctx: IEC61131Parser.IlSInstrContext) =
            oneOf<IlInstr>(ctx.ilExpr(), ctx.ilFormalFunctionCall(), ctx.ilSimple(), ctx.ilFunctionCall())!!

    override fun visitIlSimple(ctx: IEC61131Parser.IlSimpleContext) = SimpleInstr(SimpleOperand.valueOf(ctx.op.text),
            ctx.ilOperand().accept(this) as IlOperand)
            .also { it.ruleContext = ctx }

    override fun visitIlExpr(ctx: IEC61131Parser.IlExprContext) = ExprInstr(ExprOperand.valueOf(ctx.op.text),
            ctx.ilOperand()?.accept(this) as? IlOperand,
            ctx.ilSInstrList()?.accept(this) as? IlBody)
            .also { it.ruleContext = ctx }

    override fun visitIlSInstrList(ctx: IEC61131Parser.IlSInstrListContext): IlBody {
        val body = IlBody()
        ctx.ilSInstr().forEach {
            body += it.accept(this) as IlInstr
        }
        return body
    }

    override fun visitIlFunctionCall(ctx: IEC61131Parser.IlFunctionCallContext) = FunctionCallInstr(ctx.symbolic_variable().accept(this) as SymbolicReference,
            ctx.ilOperand().map { it.accept(this) as IlOperand }.toMutableList())
            .also { it.ruleContext = ctx }

    override fun visitIlFormalFunctionCall(ctx: IEC61131Parser.IlFormalFunctionCallContext): CallInstr {
        return CallInstr(CallOperand.IMPLICIT_CALLED,
                ctx.symbolic_variable().accept(this) as SymbolicReference,
                ctx.il_param_assignment().map { it.accept(this) as IlParameter }.toMutableList())
                .also { it.ruleContext = ctx }
    }

    override fun visitIlJump(ctx: IEC61131Parser.IlJumpContext) = JumpInstr(JumpOperand.valueOf(ctx.op.text), ctx.label.text)
            .also { it.ruleContext = ctx }

    override fun visitIlCall(ctx: IEC61131Parser.IlCallContext): CallInstr {
        val callInstr = CallInstr(CallOperand.valueOf(ctx.op.text),
                ctx.symbolic_variable().accept(this) as SymbolicReference,
                ctx.il_param_assignment()
                        .map { it.accept(this) as IlParameter }.toMutableList())

        val seq = if (ctx.LPAREN() != null) {
            ctx.ilOperand()
                    .map { it.accept(this) as IlOperand }
                    .map { IlParameter(right = it) }
        } else {
            ctx.il_param_assignment().map { it.accept(this) as IlParameter }
        }
        callInstr.parameters = seq.toMutableList()

        return callInstr
    }

    override fun visitIlOperand(ctx: IEC61131Parser.IlOperandContext): Any {
        if (ctx.constant() != null) {
            val const = ctx.constant()!!.accept(this) as Literal
            return IlOperand.Constant(const).also { it.ruleContext = ctx.symbolic_variable() }
        }

        if (ctx.symbolic_variable() != null) {
            val a = ctx.symbolic_variable()
            val sr = a.accept(this) as SymbolicReference
            return IlOperand.Variable(sr).also { it.ruleContext = ctx.symbolic_variable() }
        }

        throw IllegalStateException()
    }

    override fun visitIl_param_assignment(ctx: IEC61131Parser.Il_param_assignmentContext): IlParameter {
        return IlParameter(negated = ctx.NOT() != null, input = ctx.ASSIGN() != null,
                left = ctx.id.text,
                right = if (ctx.ASSIGN() != null)
                    ctx.arg.accept(this) as IlOperand
                else
                    IlOperand.Variable(SymbolicReference(ctx.target.text))
        )

    }
    //endregion

    override fun visitFbBody(ctx: IEC61131Parser.FbBodyContext): FbdBody {
        val json = ctx.FBD_CODE().text.removeSurrounding("(***FBD", "***)").trim()
        return FbdBody.fromJson(json)
    }
}
