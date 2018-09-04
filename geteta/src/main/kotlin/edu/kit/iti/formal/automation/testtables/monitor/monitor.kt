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
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.*
import edu.kit.iti.formal.smv.SMVAstVisitor
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.ast.SBinaryOperator.*
import edu.kit.iti.formal.smv.conjunction
import java.math.BigInteger

interface MonitorGeneration {
    fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): String
}

object MonitorGenerationST : MonitorGeneration {
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): String {
        val mg = MonitorGenerationSTImpl(gtt, automaton)
        val elements = mg.call()
        return IEC61131Facade.print(elements, true)
    }

    /**
     * @author Alexander Weigl
     * @version 1 (23.03.17)
     */
    class MonitorGenerationSTImpl(private val gtt: GeneralizedTestTable,
                                  private val automaton: TestTableAutomaton) {
        private val fb = FunctionBlockDeclaration()
        private val stBody = StatementList()

        val errorOutput = VariableDeclaration("ERROR_OUTPUT", VariableDeclaration.OUTPUT, AnyBit.BOOL)
        val errorInput = VariableDeclaration("ERROR_INPUT", VariableDeclaration.OUTPUT, AnyBit.BOOL)
        val resets = VariableDeclaration("RESETS", VariableDeclaration.OUTPUT, UINT)

        fun call(): PouElements {
            fb.stBody = stBody
            gtt.programVariables
                    .map { VariableDeclaration(it.name, VariableDeclaration.INPUT, it.dataType) }
                    .forEach { fb.scope.variables.add(it) }

            fb.scope.add(errorInput)
            fb.scope.add(errorOutput)
            fb.scope.add(resets)

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
            updateStateVariables()
            resets()
            return PouElements(mutableListOf(fb))
        }

        private fun resets() {
            val inputs = automaton.initialStates
                    .map { SymbolicReference((it as RowState).row.defInput.name) }
                    .reduce { a: Expression, b: Expression -> a or b }
            val error = SymbolicReference(automaton.stateError.name)
            val rst = SymbolicReference(resets.name)

            stBody.add(
                    Statements.ifthen(error and inputs,
                            error assignTo BooleanLit.LFALSE,
                            rst assignTo (rst plus IntegerLit(INT, 1.toBigInteger()))
                    ))
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

private fun SMVExpr.toStExpression(): Expression = this.accept(SMVToStVisitor)

object SMVToStVisitor : SMVAstVisitor<Expression> {
    override fun visit(top: SMVAst): Expression {
        TODO("not implemented")
    }

    override fun visit(v: SVariable): Expression = SymbolicReference(v.name.removePrefix("code\$"))
    override fun visit(be: SBinaryExpression): Expression = BinaryExpression(be.left.accept(this), operator(be.operator), be.right.accept(this))

    private fun operator(operator: SBinaryOperator): BinaryOperator =
            when (operator) {
                PLUS -> Operators.ADD
                MINUS -> Operators.SUB
                DIV -> Operators.DIV
                MUL -> Operators.MULT
                AND -> Operators.AND
                OR -> Operators.OR
                LESS_THAN -> Operators.LESS_THAN
                LESS_EQUAL -> Operators.LESS_EQUALS
                GREATER_THAN -> Operators.GREATER_THAN
                GREATER_EQUAL -> Operators.GREATER_EQUALS
                XOR -> Operators.XOR
                XNOR -> TODO()
                EQUAL -> Operators.EQUALS
                IMPL -> TODO()
                EQUIV -> TODO()
                NOT_EQUAL -> Operators.NOT_EQUALS
                MOD -> Operators.MOD
                SHL -> TODO()
                SHR -> TODO()
                WORD_CONCAT -> TODO()
            }

    override fun visit(ue: SUnaryExpression): Expression {
        return UnaryExpression(operator(ue.operator), ue.expr.accept(this))
    }

    private fun operator(operator: SUnaryOperator): UnaryOperator =
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

private infix fun SymbolicReference.assignTo(expr: Expression) = AssignmentStatement(this, expr)
