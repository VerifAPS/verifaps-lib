package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.FALSE
import edu.kit.iti.formal.automation.datatypes.values.TRUE
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.st.Statements
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.apps.bindsConstraintVariable
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.ConstraintVariable
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.Variable
import edu.kit.iti.formal.automation.testtables.model.automata.*
import edu.kit.iti.formal.smv.SMVAstDefaultVisitorNN
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.conjunction
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.09.18)
 */
object MonitorGenerationST : MonitorGeneration {
    override val key: String = "st"

    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): Monitor {
        val mg = MonitorGenerationSTImpl(gtt, automaton)
        val elements = mg.call()
        return Monitor(body = IEC61131Facade.print(elements, true))
    }

    /**
     * @author Alexander Weigl
     * @version 1 (23.03.17)
     */
    class MonitorGenerationSTImpl(private val gtt: GeneralizedTestTable,
                                  private val automaton: TestTableAutomaton) {
        private val fb = FunctionBlockDeclaration()
        private val stBody = StatementList()

        val userReset = VariableDeclaration("FORCE_RST", VariableDeclaration.INPUT, AnyBit.BOOL)
        val errorOutput = VariableDeclaration("ERROR", VariableDeclaration.OUTPUT, AnyBit.BOOL)
        val lostSync = VariableDeclaration("LOST_SYNC", VariableDeclaration.OUTPUT, AnyBit.BOOL)
        val resets = VariableDeclaration("RESETS", VariableDeclaration.OUTPUT, UINT)

        fun call(): PouElements {
            fb.name = "${gtt.name}Monitor"
            fb.stBody = stBody
            gtt.programVariables
                    .map { VariableDeclaration(it.name, VariableDeclaration.INPUT, it.dataType) }
                    .forEach { fb.scope.variables.add(it) }

            gtt.constraintVariables
                    .map { VariableDeclaration(it.name, VariableDeclaration.LOCAL, it.dataType) }
                    .forEach { fb.scope.variables.add(it) }

            gtt.constraintVariables
                    .map { VariableDeclaration("${it.name}_bound", VariableDeclaration.LOCAL, AnyBit.BOOL) }
                    .forEach { fb.scope.variables.add(it) }

            fb.scope.add(lostSync)
            fb.scope.add(errorOutput)
            fb.scope.add(resets)
            fb.scope.add(userReset)

            automaton.rowStates.values.flatMap { it }.forEach {
                val vd = VariableDeclaration(it.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
                vd.initValue = if (it in automaton.initialStates) TRUE else FALSE
                fb.scope.add(vd)
            }
            automaton.rowStates.forEach { tr, rs ->
                fb.scope.add(VariableDeclaration(tr.defFailed.name, VariableDeclaration.TEMP, AnyBit.BOOL))
                fb.scope.add(VariableDeclaration(tr.defForward.name, VariableDeclaration.TEMP, AnyBit.BOOL))
                fb.scope.add(VariableDeclaration(tr.defInput.name, VariableDeclaration.TEMP, AnyBit.BOOL))
                fb.scope.add(VariableDeclaration(tr.defOutput.name, VariableDeclaration.TEMP, AnyBit.BOOL))
                fb.scope.add(VariableDeclaration(tr.defProgress.name, VariableDeclaration.TEMP, AnyBit.BOOL))
                updateAuxVariables(tr)
            }
            bindFreeVariables()
            resets()
            updateStateVariables()
            updateOutput()

            fb.comment = "\n" + GetetaFacade.print(gtt) + "\n"

            return PouElements(mutableListOf(
                    fb))
        }

        private fun bindFreeVariables() {
            gtt.constraintVariables.forEach { fvar ->
                val boundFlag = SymbolicReference("${fvar.name}_bound")
                automaton.rowStates.forEach { row, states ->
                    val oneOfRowStates = states.map { SymbolicReference(it.name) }
                            .disjunction()
                    row.rawFields.forEach { pvar, ctx ->
                        val bind = bindsConstraintVariable(ctx, fvar)
                        if (bind) {
                            stBody.add(0, Statements.ifthen(boundFlag.not() and oneOfRowStates,
                                    SymbolicReference(fvar.name) assignTo SymbolicReference(pvar.name),
                                    boundFlag assignTo BooleanLit.LTRUE
                            ))
                        }
                    }
                }
            }
        }

        private fun updateOutput() {
            val error = SymbolicReference(errorOutput.name)
            val synclost = SymbolicReference(lostSync.name)

            val noStateOccupied = automaton.rowStates.values.flatMap { it }
                    .map { SymbolicReference(it.name) }
                    .reduce { a: Expression, b: Expression -> a or b }
                    .not()

            stBody.add(synclost assignTo noStateOccupied)
            stBody.add(error assignTo (synclost and SymbolicReference(automaton.stateError.name)))
        }

        private fun resets() {
            val inputs = automaton.initialStates
                    .map { SymbolicReference((it as RowState).row.defInput.name) }
                    .reduce { a: Expression, b: Expression -> a or b }
            val rst = resets.ref()

            val s = IfStatement()
            val statements = StatementList()

            statements.add(errorOutput.ref() assignTo BooleanLit.LFALSE)
            statements.add(SymbolicReference(automaton.stateError.name) assignTo BooleanLit.LFALSE)
            statements.add(SymbolicReference(automaton.stateSentinel.name) assignTo BooleanLit.LFALSE)

            statements.add(rst assignTo (rst plus IntegerLit(INT, 1.toBigInteger())))
            automaton.rowStates.values.flatMap { it }
                    .map {
                        SymbolicReference(it.name) assignTo
                                (if (it in automaton.initialStates) BooleanLit.LTRUE else BooleanLit.LFALSE)
                    }
                    .forEach {
                        statements.add(it)
                    }
            gtt.constraintVariables.forEach {
                statements.add(SymbolicReference("${it.name}_bound") assignTo BooleanLit.LFALSE)
            }
            s.addGuardedCommand((lostSync.ref() and inputs) or userReset.ref(), statements)
            stBody.add(s)
        }

        private fun updateStateVariables() {
            val transitions = automaton.transitions.groupBy { it.to }
            automaton.rowStates.values.flatMap { it }.forEach { createNext(transitions, it) }
            createNext(transitions, automaton.stateError)
            createNext(transitions, automaton.stateSentinel)
        }

        private fun createNext(transitions: Map<AutomatonState, List<Transition>>, it: AutomatonState) {
            val to = SymbolicReference(it.name)
            val expr =
                    transitions[it]?.map { t ->
                        val from = t.from as? RowState
                        val fromName = SymbolicReference(t.from.name)
                        when (t.type) {
                            TransitionType.ACCEPT ->
                                SymbolicReference(from!!.row.defInput.name) and fromName
                            TransitionType.ACCEPT_PROGRESS ->
                                SymbolicReference(from!!.row.defProgress.name) and fromName
                            TransitionType.FAIL ->
                                SymbolicReference(from!!.row.defFailed.name) and fromName
                            TransitionType.TRUE ->
                                fromName
                        }
                    }?.reduce { a, b -> a or b }
                            ?: BooleanLit.LFALSE

            stBody.add(to assignTo expr)
        }

        private fun updateAuxVariables(tr: TableRow) {
            val defInput = SymbolicReference(tr.defInput.name)
            val defOutput = SymbolicReference(tr.defOutput.name)
            val defFailed = SymbolicReference(tr.defFailed.name)
            val defForward = SymbolicReference(tr.defForward.name)
            val defProgress = SymbolicReference(tr.defProgress.name)

            val progress = tr.outgoing.map { SymbolicReference(it.defInput.name) }
                    .reduce { acc: Expression, v: Expression -> acc or v }

            val s = arrayListOf(
                    defInput assignTo tr.inputExpr.values.conjunction().toStExpression(),
                    defOutput assignTo tr.outputExpr.values.conjunction().toStExpression(),
                    defFailed assignTo (defInput and defOutput.not()),
                    defForward assignTo (defInput and defOutput))
            stBody.addAll(0, s)
            stBody.add(stBody.lastIndex,
                    defProgress assignTo ((defInput and defOutput) and progress.not()))
        }
    }
}

private fun TableRow.containsVariable(fvar: Variable) =
        (inputExpr.values + outputExpr.values).find { fvar in it }

operator fun SMVExpr.contains(fvar: Variable): Boolean =
        accept(object : SMVAstDefaultVisitorNN<Boolean>() {
            override fun defaultVisit(top: SMVAst) = false
            override fun visit(v: SVariable) =
                    v.name == fvar.name

            override fun visit(be: SBinaryExpression) =
                    be.left.accept(this) || be.right.accept(this)

            override fun visit(ue: SUnaryExpression) = ue.expr.accept(this)

            override fun visit(ce: SCaseExpression): Boolean {
                for (case in ce.cases) {
                    if (case.condition.accept(this)) return true
                    if (case.then.accept(this)) return true
                }
                return false
            }

            override fun visit(func: SFunction): Boolean = func.arguments.any { it.accept(this) }
        })

private fun VariableDeclaration.ref() = SymbolicReference(name)

//TODO should be externalize into Symbex!
private fun SMVExpr.toStExpression(): Expression = this.accept(SMVToStVisitor)

object SMVToStVisitor : SMVAstVisitor<Expression> {
    override fun visit(top: SMVAst): Expression {
        TODO("not implemented")
    }

    override fun visit(v: SVariable): Expression = SymbolicReference(v.name.removePrefix("code\$"))
    override fun visit(be: SBinaryExpression): Expression = BinaryExpression(be.left.accept(this), operator(be.operator), be.right.accept(this))

    fun operator(operator: SBinaryOperator): BinaryOperator =
            when (operator) {
                SBinaryOperator.PLUS -> Operators.ADD
                SBinaryOperator.MINUS -> Operators.SUB
                SBinaryOperator.DIV -> Operators.DIV
                SBinaryOperator.MUL -> Operators.MULT
                SBinaryOperator.AND -> Operators.AND
                SBinaryOperator.OR -> Operators.OR
                SBinaryOperator.LESS_THAN -> Operators.LESS_THAN
                SBinaryOperator.LESS_EQUAL -> Operators.LESS_EQUALS
                SBinaryOperator.GREATER_THAN -> Operators.GREATER_THAN
                SBinaryOperator.GREATER_EQUAL -> Operators.GREATER_EQUALS
                SBinaryOperator.XOR -> Operators.XOR
                SBinaryOperator.XNOR -> TODO()
                SBinaryOperator.EQUAL -> Operators.EQUALS
                SBinaryOperator.IMPL -> TODO()
                SBinaryOperator.EQUIV -> TODO()
                SBinaryOperator.NOT_EQUAL -> Operators.NOT_EQUALS
                SBinaryOperator.MOD -> Operators.MOD
                SBinaryOperator.SHL -> TODO()
                SBinaryOperator.SHR -> TODO()
                SBinaryOperator.WORD_CONCAT -> TODO()
            }

    override fun visit(ue: SUnaryExpression): Expression {
        return UnaryExpression(operator(ue.operator), ue.expr.accept(this))
    }

    fun operator(operator: SUnaryOperator): UnaryOperator =
            when (operator) {
                SUnaryOperator.NEGATE -> Operators.NOT
                SUnaryOperator.MINUS -> Operators.MINUS
            }

    override fun visit(l: SLiteral): Expression {
        val v = l.value
        return when (v) {
            is BigInteger -> IntegerLit(INT, v)
            is Long -> IntegerLit(INT, v.toBigInteger())
            is Boolean -> if (v) BooleanLit.LTRUE else BooleanLit.LFALSE
            is String -> EnumLit(null, v)
            else -> {
                println(v)
                TODO(v.javaClass.toString())
            }
        }
    }

    override fun visit(a: SAssignment): Expression {
        TODO("not implemented")
    }

    override fun visit(ce: SCaseExpression): Expression {
        TODO("not implemented")
    }

    override fun visit(smvModule: SMVModule): Expression {
        TODO("not implemented")
    }

    override fun visit(func: SFunction): Expression {
        return Invocation(func.name,
                func.arguments.map { it.accept(this) }
        )
    }

    override fun visit(quantified: SQuantified): Expression {
        TODO("not implemented")
    }
}
