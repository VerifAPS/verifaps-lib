package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.IEC61131Facade.fileResolve
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.values.VBool
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue.getInit
import edu.kit.iti.formal.automation.st.HccPrinter
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.SpecialCommentFactory
import edu.kit.iti.formal.automation.st.SpecialCommentMeta
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.trans.FBEmbeddCode
import edu.kit.iti.formal.automation.st0.trans.SCOPE_SEPARATOR
import edu.kit.iti.formal.automation.st0.trans.VariableRenamer
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.GetetaFacade.constructTable
import edu.kit.iti.formal.automation.testtables.GetetaFacade.readTables
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.*
import edu.kit.iti.formal.automation.testtables.monitor.SMVToStVisitor
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.meta
import java.io.File
import java.io.PrintWriter
import kotlin.math.abs

data class ReactiveProgram(
        val name: String,
        val scope: Scope = Scope(),
        val init: StatementList = StatementList(),
        val body: StatementList = StatementList(),
        val functions: MutableList<FunctionDeclaration> = ArrayList())

/**
 * Maps the value of a enum to its type.
 */
typealias EnumValueTable = Map<String, EnumerateType>

private fun createNext(t: Transition): SMVExpr {
    val stateVar = SVariable(t.from.name, SMVTypes.BOOLEAN)
    return if (t.type == TransitionType.TRUE) {
        stateVar
    } else {

        val inputExpr = (t.from as RowState).row.inputExpr.values.conjunction(SLiteral.TRUE)
        val outputExpr = (t.from as RowState).row.outputExpr.values.conjunction(SLiteral.TRUE)

        when (t.type) {
            TransitionType.ACCEPT ->
                stateVar and inputExpr and outputExpr
            TransitionType.ACCEPT_PROGRESS ->
                stateVar and inputExpr and outputExpr
            TransitionType.FAIL ->
                stateVar and inputExpr and outputExpr.not()
            TransitionType.MISS -> stateVar and inputExpr.not()
            TransitionType.TRUE -> stateVar
        }
    }
}

class GttMiterConstruction(val gtt: GeneralizedTestTable,
                           val automaton: TestTableAutomaton,
                           val enumValues: EnumValueTable) {
    private var transitions = automaton.transitions.groupBy { it.to }
    private val sentinel = VariableDeclaration(automaton.stateSentinel.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
    private val inv = VariableDeclaration("__INV__", VariableDeclaration.OUTPUT, AnyBit.BOOL)
    private val err = VariableDeclaration("error", VariableDeclaration.LOCAL, AnyBit.BOOL)

    val target = ReactiveProgram("Miter", Scope(Scope()))

    fun constructMiter(): ReactiveProgram {
        //region prepare variable scope
        translateProgramVariables()
        translateConstraintVariables()
        addHistoryVariables()
        addVariablesForAutomatonStates(automaton)

        sentinel.initValue = getInit(AnyBit.BOOL)
        target.scope.variables.add(sentinel)
        err.initValue = getInit(AnyBit.BOOL)
        target.scope.variables.add(err)
        //inv.initValue = getInit(AnyBit.BOOL)
        target.scope.variables.add(inv)
        //endregion

        //region prepare body
        addNextAssignments()
        assignFromTempVariables()
        addInvariant()
        shiftHistory()
        //endregion

        //Init
        initialiseConstraintVariables()

        target.functions.addAll(gtt.functions)

        return target
    }

    private fun initialiseConstraintVariables() {
        if (gtt.constraintVariables.isEmpty())
            return

        //havoc
        target.init += CommentStatement("havocing the contraint variables")
        gtt.constraintVariables.forEach { it ->
            val hc = SpecialCommentFactory.createHavoc(it.name, it.dataType)
            target.init.add(hc)
        }

        //assume
        val constraints = gtt.constraintVariables
            .filter{ it.constraint != null}
            .map {
            GetetaFacade.exprToSMV(it.constraint!!, SVariable(it.name), 0, gtt.parseContext)
            }
        val combinedConstraints = constraints.conjunction(SLiteral.TRUE).translateToSt()
        target.init += SpecialCommentFactory.createAssume(combinedConstraints)
    }

    private fun assignFromTempVariables() {
        automaton.getRowStates().forEach { rowState ->
            target.body += (rowState.name assignTo "_${rowState.name}")
        }
    }

    private fun addNextAssignments() {
        gtt.region.flat().forEach { tr ->
            automaton.getStates(tr)?.forEach { state ->
                val expr = createNext(state)
                target.body += "_${state.name}" assignTo expr
            }
        }
        target.body.add(err.name assignTo createNext(automaton.stateError))
        target.body.add(sentinel.name assignTo createNext(automaton.stateSentinel))
    }

    private fun addInvariant() {
        val invAssign: SMVExpr = automaton.getRowStates()
                .map { SVariable(it.name, SMVTypes.BOOLEAN) }
                .asIterable()
                .disjunction()
                .or(SVariable(sentinel.name, SMVTypes.BOOLEAN))
                .or(SVariable(err.name, SMVTypes.BOOLEAN).not())
        target.body.add("__INV__" assignTo invAssign.translateToSt())
        val assert = SpecialCommentFactory
                .createAssert(SymbolicReference("__INV__"));
        target.body.add(assert)
    }

    private fun addVariablesForAutomatonStates(automaton: TestTableAutomaton) {
        automaton.getRowStates().forEach { rowState ->
            val vd1 = VariableDeclaration(rowState.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
            val vd2 = VariableDeclaration("_" + rowState.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
            vd1.initValue = getInit(AnyBit.BOOL)
            if (automaton.initialStates.contains(rowState)) {
                vd1.initValue = VBool(AnyBit.BOOL, true)
            }
            vd2.initValue = getInit(AnyBit.BOOL)
            target.scope.variables.add(vd1)
            target.scope.variables.add(vd2)
        }
    }

    private val exprConverter = ExpressionConversion(enumValues).also {
        for ((a, b) in gtt.parseContext.refs) {
            for (n in (1..abs(b))) {
                val ref = gtt.parseContext.getReference(a, -n)
                it.variableReplacement[ref.name] = historyName(a.name, n)
            }
        }
    }

    private fun createNext(state: AutomatonState): Expression {
        val expr: List<SMVExpr>? = transitions[state]?.map { createNext(it) }
        val a: SMVExpr = expr?.disjunction() ?: SLiteral.FALSE
        return a.translateToSt()
    }

    private fun addHistoryVariables() {
        gtt.parseContext.refs.forEach { (svar, maxhis) ->
            for (n in (1..abs(maxhis))) {
                val dt = gtt.programVariables.find { it.name == svar.name }?.dataType
                        ?: error("Could not find datatype for SVariable: `${svar.name}")
                val vd = VariableDeclaration(historyName(svar.name, n), VariableDeclaration.LOCAL,
                        if (dt is EnumerateType) INT else dt)
                vd.initValue = getInit(vd.dataType!!)
                target.scope.variables.add(vd)
            }
        }
    }

    private fun shiftHistory() {
        gtt.parseContext.refs.forEach { (svar, maxhis) ->
            val names = (1..abs(maxhis)).map { historyName(svar.name, it) }.toMutableList()
            names.add(0, svar.name)
            names.asReversed().zipWithNext().forEach { (old, new) ->
                target.body += old assignTo new
            }
        }
    }

    private fun translateConstraintVariables() {
        gtt.constraintVariables.forEach { cv ->
            val vd = VariableDeclaration(cv.name, VariableDeclaration.LOCAL, cv.dataType)
            if (cv.dataType is EnumerateType) {
                cv.dataType = INT
            }
            vd.initValue = getInit(cv.dataType)
            target.scope.variables.add(vd)
        }
    }

    private fun translateProgramVariables() {
        gtt.programVariables.forEach { pv ->
            val vd = VariableDeclaration(pv.name, VariableDeclaration.INPUT, pv.dataType)
            if (pv.dataType is EnumerateType) {
                pv.dataType = INT
            }
            vd.initValue = getInit(pv.dataType)
            target.scope.variables.add(vd)
        }
    }

    private fun SMVExpr.translateToSt(): Expression = this.accept(exprConverter)
}

fun historyName(s: String, n: Int) = "_h_${s}_$n"

class ProgMiterConstruction(val exec: PouExecutable) {
    constructor(exec: PouElements) : this(exec.findFirstProgram()!!) {
        exec.forEach {
            when (it) {
                is TypeDeclarations -> addTypeDeclaration(it)
                is FunctionDeclaration -> addFunctionDeclaration(it)
            }
        }
    }

    val target = ReactiveProgram(exec.name, exec.scope)

    fun addFunctionDeclaration(func: FunctionDeclaration) = target.functions.add(func)

    fun addTypeDeclaration(decls: TypeDeclarations) {
        decls.forEach { td ->
            when (td) {
                is EnumerationTypeDeclaration -> {
                    td.allowedValues.forEachIndexed { i, value ->
                        val vd = VariableDeclaration(
                                "${td.name}__${value.text.toUpperCase()}",
                                VariableDeclaration.CONSTANT,
                                SimpleTypeDeclaration(INT, IntegerLit(i)))
                        target.scope.topLevel.add(vd)
                    }

                    val fdecl = FunctionDeclaration("nondet_${td.name.toLowerCase()}",
                            returnType = RefTo(INT))
                    fdecl.scope.add(VariableDeclaration("x", VariableDeclaration.LOCAL, INT))
                    fdecl.stBody = StatementList().also {
                        val x = SymbolicReference("x")
                        val assume = td.values.map {
                            x eq IntegerLit(INT, it.toBigInteger())
                        }.disjunction()
                        it.add(SpecialCommentFactory.createHavoc("x", INT))
                        it.add(SpecialCommentFactory.createAssume(assume))
                    }
                    target.functions.add(fdecl)
                }
                else -> error("Found unsupported declared type: $td")
            }
        }
    }

    fun constructMiter(): ReactiveProgram {
        target.body.addAll(exec.stBody!!)
        return target
    }
}

class ExpressionConversion(val enumValues: EnumValueTable) : SMVAstVisitor<Expression> {
    val variableReplacement: HashMap<String, String> = HashMap()

    override fun visit(top: SMVAst): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(v: SVariable): Expression {
        val n = variableReplacement.getOrDefault(v.name, v.name)
        return SymbolicReference(n)
    }

    override fun visit(be: SBinaryExpression): Expression = BinaryExpression(be.left.accept(this),
            SMVToStVisitor.operator(be.operator), be.right.accept(this))

    override fun visit(ue: SUnaryExpression): Expression = UnaryExpression(SMVToStVisitor.operator(ue.operator), ue.expr.accept(this))

    override fun visit(l: SLiteral): Expression {
        return when (l.dataType) {
            is SMVTypes.BOOLEAN -> BooleanLit(l.value == true)
            is SMVWordType -> IntegerLit(INT, l.value.toString().toBigInteger())
            is EnumType -> {
                val et = enumValues[l.value.toString().toUpperCase()]
                        ?: error("No enum defined which contains ${l.value}. Defined values: ${enumValues.keys}")
                EnumLit(et, l.value.toString())
            }
            else -> error("Literals of type '${l.javaClass} are not supported")
        }
    }

    override fun visit(a: SAssignment): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(ce: SCaseExpression): Expression {
        fun ifThenElse(cases: List<SCaseExpression.Case>, n: Int): Expression {
            if (n >= cases.size) {
                throw IllegalArgumentException()
            }

            if (n == cases.size - 1) {//last element
                // ignoring the last condition for well-definedness
                return cases[n].then.accept(this)
            }

            val ite = Invocation("SEL",
                    cases[n].condition.accept(this),
                    cases[n].then.accept(this),
                    ifThenElse(cases, n + 1))
            return ite
        }
        return ifThenElse(ce.cases, 0)
    }

    override fun visit(smvModule: SMVModule): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(func: SFunction): Expression {
        return Invocation(func.name,
                func.arguments.map { it.accept(this) }
        )
    }

    override fun visit(quantified: SQuantified): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}

class SimpleProductProgramBuilder(name: String = "main") {
    val target = ReactiveProgram(name)

    fun combine(vararg programs: ReactiveProgram) {
        programs.forEach { add(it) }
    }

    fun add(program: ReactiveProgram) {
        target.scope.addVariables(program.scope)
        target.init.addAll(program.init)
        target.body.addAll(program.body)
        target.functions.addAll(program.functions)
    }

    fun build(): PouExecutable {
        val target = target.toProgram()
        return SymbExFacade.simplify(target)
    }
}

class InvocationBasedProductProgramBuilder(name: String = "main") {
    val target = ReactiveProgram(name).also {
        it.scope.parent = Scope()
    }
    private val definedVariables = HashMap<String, SymbolicReference>()

    init {
        FBEmbeddCode.renaming = { a, b, prefix ->
            VariableRenamerSC(a.scope::isGlobalVariable, b.clone(), prefix).rename()
        }
    }

    fun combine(vararg programs: ReactiveProgram) {
        programs.forEach { add(it) }
    }

    private fun createInstance(p: ReactiveProgram, fbd: FunctionBlockDeclaration): VariableDeclaration {
        val vd = VariableDeclaration(p.name.toLowerCase(), VariableDeclaration.LOCAL, FunctionBlockDataType(fbd))
        target.scope.add(vd)
        return vd

    }

    private fun createParameters(p: ReactiveProgram): MutableList<InvocationParameter> {
        return p.scope.variables.filter { it.isInput }.map {
            InvocationParameter(it.name, false, findOrCreateInput(it))
        }.toMutableList()
    }

    // looks up a given variable, if it is already declared as an output of a previous program
    // returns a ref to it, else an input variable is declared
    private fun findOrCreateInput(it: VariableDeclaration): Expression = definedVariables.computeIfAbsent(it.name) { k ->
        val vd = it.clone()
        vd.type = VariableDeclaration.LOCAL
        target.scope.add(vd)
        target.body += SpecialCommentFactory.createHavoc(it.name, it.dataType!!)
        SymbolicReference(it.name)
    }

    fun add(program: ReactiveProgram) {
        val fbd = program.asFunctionBlock()
        val instance = createInstance(program, fbd)
        val parameter = createParameters(program)
        val invocation = InvocationStatement(SymbolicReference(instance.name), parameter)
        invocation.invoked = Invoked.FunctionBlock(fbd)

        val renamed = VariableRenamerSC(program.scope::isGlobalVariable, program.init.clone()) { instance.name + SCOPE_SEPARATOR + it }
        target.init.addAll(renamed.rename())

        //will be rewritten by simplify
        target.body.add(invocation)

        target.functions.addAll(program.functions)

        program.scope.parent?.variables?.let {
            target.scope.parent?.variables?.addAll(it)
        }

        announceOutputs(instance, program)
    }

    private fun announceOutputs(instance: VariableDeclaration, program: ReactiveProgram) {
        program.scope.variables.filter { it.isOutput }
                .forEach {
                    definedVariables[it.name] = SymbolicReference(instance.name, SymbolicReference(it.name))
                }
    }

    fun build(b: Boolean): PouExecutable {
        val target = target.toProgram()
        if (b)
            return SymbExFacade.simplify(target)
        else
            return target
    }
}

/**
 * Renames everything
 */
class VariableRenamerSC(isGlobal: (SymbolicReference) -> Boolean,
                        statements: StatementList,
                        newName: (String) -> String)
    : VariableRenamer(isGlobal, statements, newName) {
    val commentsRenamer = SpecialCommentRenamer(isGlobal, newName, this)
    override fun visit(commentStatement: CommentStatement): CommentStatement {
        return commentStatement.accept(commentsRenamer) as CommentStatement
    }
}

/**
 * Renames only SpecialComments and below
 */
class SpecialCommentRenamer(val isGlobal: (SymbolicReference) -> Boolean,
                            val newName: (String) -> String,
                            val renamer: AstMutableVisitor) : AstMutableVisitor() {
    override fun visit(commentStatement: CommentStatement): CommentStatement {
        when (val meta = commentStatement.meta<SpecialCommentMeta>()) {
            is SpecialCommentMeta.AssertComment -> {
                meta.expr = meta.expr.accept(renamer) as Expression
            }
            is SpecialCommentMeta.AssumeComment -> {
                meta.expr = meta.expr.accept(renamer) as Expression
            }
            is SpecialCommentMeta.HavocComment -> {
                if (!isGlobal(SymbolicReference(meta.variable))) {
                    meta.variable = newName(meta.variable)
                }
            }
            else -> {}
        }
        return commentStatement
    }
}

private fun ReactiveProgram.toProgram(): ProgramDeclaration {
    val stmts = StatementList()
    stmts.addAll(init)
    stmts.add(WhileStatement(BooleanLit.LTRUE, body))
    return ProgramDeclaration(name, scope, stmts)
}

private fun ReactiveProgram.asFunctionBlock(): FunctionBlockDeclaration {
    return FunctionBlockDeclaration(name, scope, body)
}

fun main() = run {
    SCOPE_SEPARATOR = "__"
    //choose gtt
    run("geteta/examples/LinRe/lr.st",
            "geteta/examples/LinRe/lr.gtt")
}

fun run(programFile: String, table: String) {
    //region read table
    val gtt = readTables(File(table)).first()
    gtt.programRuns = listOf("")
    gtt.generateSmvExpression()
    val gttAsAutomaton = constructTable(gtt).automaton
    //endregion

    //region read program
    val progs = fileResolve(File(programFile)).first
    //endprogram

    val enum = progs.findFirstProgram()?.scope?.enumValuesToType() ?: mapOf()
    val miter = GttMiterConstruction(gtt, gttAsAutomaton, enum).constructMiter()
    val program = ProgMiterConstruction(progs.findFirstProgram()!!).let { p ->
        progs.forEach {
            when (it) {
                is TypeDeclarations -> p.addTypeDeclaration(it)
                is FunctionDeclaration -> p.addFunctionDeclaration(it)
            }
        }
        p.constructMiter()
    }

    val productProgramBuilder = InvocationBasedProductProgramBuilder()
    productProgramBuilder.add(program)
    productProgramBuilder.add(miter)
    val productProgram = productProgramBuilder.build(false)
    PrintWriter(System.out).use { out ->
        val hccprinter = HccPrinter(CodeWriter(out))
        hccprinter.isPrintComments = true
        productProgram.accept(hccprinter)

        hccprinter.isPrintComments = true
        SymbExFacade.simplify(productProgram).accept(hccprinter)
    }
}