package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.automation.blocks.getRandomLabel
import edu.kit.iti.formal.automation.exceptions.FunctionInvocationArgumentNumberException
import edu.kit.iti.formal.automation.exceptions.UnknownDatatype
import edu.kit.iti.formal.automation.exceptions.UnknownVariableException
import edu.kit.iti.formal.automation.il.IlSymbex
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.rvt.translators.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.Invoked.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import java.util.*
import java.util.concurrent.atomic.AtomicInteger

typealias LineMap = HashMap<Int, Pair<String, Position>>

/**
 * Created by weigl on 26.11.16.
 * 2019-08-11 weigl: use definition for common sub expressions (<var>_<linenumer> value of <variable> in linenumber)
 *                   <var> refers to the last <variable>
 */
open class SymbolicExecutioner() : DefaultVisitor<SMVExpr>() {
    override fun defaultVisit(obj: Any) = throw IllegalStateException("Symbolic Executioner does not handle $obj")

    var scope: Scope = Scope.defaultScope()
    private val varCache = HashMap<String, SVariable>()
    var operationMap: OperationMap = DefaultOperationMap()
    var typeTranslator: TypeTranslator = DefaultTypeTranslator()
    var valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue

    private val state = Stack<SymbolicState>()
    private var globalState = SymbolicState()
    private var caseExpression: Expression? = null

    init {
        push(SymbolicState(globalState))
    }

    constructor(globalScope: Scope?) : this() {
        if (globalScope != null)
            this.scope = globalScope
    }

    fun peek(): SymbolicState {
        return state.peek()
    }

    fun pop(): SymbolicState {
        return state.pop()
    }
    //endregion

    @JvmOverloads
    fun push(map: SymbolicState = SymbolicState(peek())) {
        state.push(map)
    }

    fun lift(vd: VariableDeclaration): SVariable {
        try {
            return varCache.computeIfAbsent(vd.name) { this.typeTranslator.translate(vd) }
        } catch (e: NullPointerException) {
            throw UnknownDatatype("Datatype not given/inferred for variable $vd ${vd.dataType}", e)
        }

    }

    fun lift(vd: SymbolicReference): SVariable {
        return if (varCache.containsKey(vd.identifier))
            varCache[vd.identifier]!!
        else {
            val v = peek().keys.find { name ->
                vd.identifier == name.name
            }
            if (v != null) {
                varCache[vd.identifier] = v
                return v
            } else
                throw UnknownVariableException("Variable access to not declared variable: ${IEC61131Facade.print(vd)}. Line: ${vd.startPosition}")
        }
    }

    //region rewriting of expressions using the current state
    override fun visit(binaryExpression: BinaryExpression): SMVExpr {
        val left = binaryExpression.leftExpr.accept(this)!!
        val right = binaryExpression.rightExpr.accept(this)!!
        return this.operationMap
                .translateBinaryOperator(left, binaryExpression.operator, right)
    }

    override fun visit(u: UnaryExpression): SMVExpr {
        val left = u.expression.accept(this)!!
        return this.operationMap.translateUnaryOperator(u.operator, left)
    }

    override fun visit(symbolicReference: SymbolicReference): SMVExpr {
        return peek()[lift(symbolicReference)]
                ?: throw IllegalStateException("Could not resolve access to '${symbolicReference.toHuman()}'.")
        /* Enum already be resoled
        if (symbolicReference.dataType is EnumerateType && (symbolicReference.dataType as EnumerateType)
                        .allowedValues.contains(symbolicReference.identifier))
            this.valueTranslator.translate(VAnyEnum(
                    symbolicReference.dataType as EnumerateType,
                    symbolicReference.identifier))
        else*/
    }

    //endregion

    //region visitors
    override fun visit(literal: Literal): SLiteral {
        return this.valueTranslator.translate(literal)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) = visit(functionBlockDeclaration as PouExecutable)
    override fun visit(programDeclaration: ProgramDeclaration): SCaseExpression? = visit(programDeclaration as PouExecutable)
    fun visit(programDeclaration: PouExecutable): SCaseExpression? {
        scope = programDeclaration.scope

        push(SymbolicState())

        // initialize root state
        for (vd in scope) {
            val s = lift(vd)
            assign(vd, s)
        }

        globalState = SymbolicState()
        for (variable in scope.filterByFlags(VariableDeclaration.GLOBAL))
            globalState[lift(variable)] = peek()[lift(variable)]!!

        programDeclaration.stBody!!.accept(this)
        return null
    }

    override fun visit(assign: AssignmentStatement): SMVExpr? {
        val expr = assign.expression.accept(this)!!
        assign(assign.location, expr)
        return null
    }

    override fun visit(statements: StatementList): SCaseExpression? {
        for (s in statements) {
            if (s is ExitStatement || s is ReturnStatement) { //TODO throw exception to handle everything
                return null
            }
            s.accept(this)
        }
        return null
    }

    /*Unsupported should already rolled out by ST0 Transformation
    override fun visit(fbc: InvocationStatement): SMVExpr {
        return visit(fbc.invocation)!!
    }*/

    override fun visit(invocation: Invocation): SMVExpr? {
        //val fd = scope.resolveFunction(invocation) ?: throw FunctionUndefinedException(invocation)
        val inv = when (val i = invocation.invoked) {
            is Action -> i.action
            is Program -> i.program
            is FunctionBlock -> i.fb
            is Invoked.Function -> i.function
            is Method -> i.method
            null -> throw IllegalStateException("Can not invoke a not resolved function: $invocation")
        }
        val returnType = when (val i = invocation.invoked) {
            is Invoked.Function -> i.function.returnType
            is Method -> i.method.returnType
            else -> throw IllegalStateException("$invocation does not have a return type.")
        }
        val stBody = (inv as? HasStBody)?.stBody
        val ilBody = (inv as? HasIlBody)?.ilBody
        val scope = (inv as? HasScope)?.scope!!
        val fName = (inv as Identifiable).name


        //initialize data structure
        val calleeState = SymbolicState(globalState)
        val callerState = peek()

        //region register function name as output variable
        if (scope.hasVariable(fName)) {
            val vd = VariableDeclaration(fName, VariableDeclaration.OUTPUT, returnType.obj!!)
            vd.initValue = initValueTranslator.getInit(returnType.obj!!)
            scope.add(vd)
        }
        //endregion

        //region local variables (declaration and initialization)
        for (vd in scope.variables) {
            //if (!calleeState.containsKey(vd.getName())) {
            val expr = this.valueTranslator.translate(vd.initValue!!)
            calleeState.assign(lift(vd), assignmentCounter.incrementAndGet(), expr) //TODO maintain map?
            //}
        }
        //endregion

        //region transfer variables
        val parameters = invocation.parameters
        val inputVars = scope.filterByFlags(
                VariableDeclaration.INPUT or VariableDeclaration.INOUT)

        if (parameters.size > inputVars.size) {
            //System.err.println(fd.getFunctionName());
            //inputVars.stream().map(VariableDeclaration::getName).forEach(System.err::println);
            throw FunctionInvocationArgumentNumberException()
        }

        for (i in parameters.indices) {
            val parameter = parameters[i]
            if (parameter.isOutput)
                continue
            if (parameter.name == null)
            // name from definition, in order of declaration, expression from caller site
                calleeState.assign(lift(inputVars[i]),
                        assignmentCounter.incrementAndGet(),
                        parameter.expression.accept(this)!!)
            else {
                val o = inputVars.stream().filter { iv -> iv.name == parameter.name }.findAny()
                if (o.isPresent) {
                    val e = parameter.expression.accept(this)!!
                    calleeState[lift(o.get())] = e
                }
            }
        }

        for (outputVar in scope.filterByFlags(VariableDeclaration.OUTPUT))
            calleeState.assign(lift(outputVar), assignmentCounter.incrementAndGet(),
                    this.valueTranslator.translate(
                            this.initValueTranslator.getInit(outputVar.dataType!!)))

        //endregion

        //region execution of body
        val returnState =
                if (stBody != null) {
                    push(calleeState)
                    stBody.accept(this)
                    pop()
                } else if (ilBody != null) {
                    val ilsymbex = IlSymbex(ilBody, scope = scope, state = calleeState)
                    ilsymbex.call()
                } else {
                    throw IllegalStateException("No executable body found for $fName")
                }

        // Update output variables
        val outputParameters = invocation.outputParameters
        val outputVars = scope.filterByFlags(
                VariableDeclaration.OUTPUT, VariableDeclaration.INOUT)

        for (parameter in outputParameters) {
            val o = outputVars.find { fName == parameter.name }
            val expr = parameter.expression
            if (o != null && parameter.expression is SymbolicReference) {
                val symVar = lift(expr as SymbolicReference)
                peek().replace(symVar, returnState[lift(o)]!!)
            }
            // TODO handle parameter.getExpression() instanceof Literal, etc.
        }
        //endregion

        /*val value = calleeState[fName] // store, because of destroying change in next lines
        calleeState.map.forEach { (t, u) ->
            // do not leak internal variables to the outside
            val variable = SVariable("${getRandomLabel()}_${t.name}", t.dataType!!);
            callerState.map[variable] = u
        }*/
        val unfolded = calleeState.unfolded()
        return unfolded.entries.find { (a, b) -> a.name == fName }?.value
    }

    override fun visit(statement: IfStatement): SCaseExpression? {
        val branchStates = SymbolicBranches()

        for ((condition1, statements) in statement.conditionalBranches) {
            val condition = condition1.accept(this)!!
            push()
            statements.accept(this)
            branchStates.addBranch(condition, pop())
        }

        push()
        statement.elseBranch.accept(this)
        branchStates.addBranch(SLiteral.TRUE, pop())

        val cur = peek()
        val combined = branchStates.asCompressed(statement.endPosition)
        cur.map.putAll(combined.map)
        return null
    }

    override fun visit(caseStatement: CaseStatement): SMVExpr? {
        val branchStates = SymbolicBranches()
        for (gs in caseStatement.cases) {
            val condition = buildCondition(caseStatement.expression, gs)
            push()
            gs.statements.accept(this)
            branchStates.addBranch(condition, pop())
        }
        push()
        caseStatement.elseCase.accept(this)
        branchStates.addBranch(SLiteral.TRUE, pop())
        val cur = peek()
        val combined = branchStates.asCompressed(caseStatement.endPosition)
        cur.map.putAll(combined.map)
        return null
    }

    private fun buildCondition(e: Expression, c: Case): SMVExpr {
        caseExpression = e
        return c.conditions
                .map { a -> a.accept(this) }
                .map { it!! }
                .reduce(SMVFacade.reducerKt(SBinaryOperator.OR))
    }

    override fun visit(r: CaseCondition.Range): SMVExpr {
        val lower = BinaryExpression(caseExpression!!, Operators.GREATER_EQUALS, r.start!!)
        val upper = BinaryExpression(r.stop!!, Operators.GREATER_EQUALS, caseExpression!!)
        val and = BinaryExpression(lower, Operators.AND, upper)
        return and.accept(this)!!
    }

    override fun visit(i: CaseCondition.IntegerCondition): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, i.value)
        return be.accept(this)!!
    }

    override fun visit(e: CaseCondition.Enumeration): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, e.start)
        return be.accept(this)!!
        //TODO rework case conditions
    }

    //ignore
    override fun visit(commentStatement: CommentStatement) = null
    //endregion


    val lineNumberMap = LineMap()
    val assignmentCounter = AtomicInteger(-1)

    fun assign(vd: VariableDeclaration, value: SMVExpr) {
        val s = lift(vd)
        val cnt = assignmentCounter.incrementAndGet()
        vd.startPosition.run {
            lineNumberMap[cnt] = vd.toHuman() to this
        }
        peek().assign(s, cnt, value)
    }

    fun assign(ref: SymbolicReference, value: SMVExpr) {
        val s = lift(ref)
        val cnt = assignmentCounter.incrementAndGet()
        ref.startPosition?.run {
            lineNumberMap[cnt] = ref.toHuman() to this
        }
        peek().assign(s, cnt, value)
    }

    fun SymbolicBranches.asCompressed(pos: Position): SymbolicState {
        val sb = SymbolicState()
        variables.forEach { (t, u) ->
            val sv = SymbolicVariable(t)
            val cnt = assignmentCounter.incrementAndGet()
            lineNumberMap[cnt] = t.name to pos
            sv.push(u.compress(), "_$cnt")
            defines[t]?.let { sv.values.putAll(it) }
            sb.map[t] = sv
        }
        return sb
    }
}

class SymbolicBranches {
    val variables: HashMap<SVariable, SCaseExpression> = HashMap()
    val defines = HashMap<SVariable, HashMap<SVariable, SMVExpr>>()

    fun addBranch(condition: SMVExpr, state: SymbolicState) {
        for ((key, value) in state.map) {
            getVariable(key).add(condition, if (state.useDefinitions) value.current else value.value!!)
            getDefines(key).putAll(value.values)
        }
    }

    fun getVariable(key: SVariable): SCaseExpression = variables.computeIfAbsent(key) { SCaseExpression() }
    fun getDefines(key: SVariable): HashMap<SVariable, SMVExpr> = defines.computeIfAbsent(key) { HashMap() }
}
