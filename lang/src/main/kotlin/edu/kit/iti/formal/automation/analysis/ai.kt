package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import org.antlr.v4.runtime.misc.Interval
import org.antlr.v4.runtime.misc.IntervalSet
import java.util.*
import kotlin.collections.HashMap
import kotlin.math.ceil
import kotlin.math.floor


typealias AState<T> = HashMap<String, T>

interface AiLattice<T> {
    val operations: AbstractOperations<T>
    fun branchReducer(a: T, b: T): T
    fun isAlwaysTrue(t: T): Boolean
    fun isAlwaysFalse(t: T): Boolean
    fun isTrueable(t: T): Boolean
    fun isFalseable(t: T): Boolean
    fun stateEquals(a: AState<T>, b: AState<T>): Boolean
}


/**
 * This class contains an API for abstract interpretation.
 * @author Alexander Weigl
 * @version 1 (06.11.19)
 */
class AbstractInterpretation<T>(val lattice: AiLattice<T>, val startSpace: AState<T>) {
    var space = startSpace;

    fun interpretFixpoint(e: PouExecutable): Map<String, T> {
        do {
            val oldSpace = HashMap(space)
            interpret(e);
            val newSpace = space
        } while (newSpace == oldSpace)
        return space;
    }

    fun interpret(e: Top): AState<T> {
        val asi = AbstractStateInterpreter(space, lattice)
        e.accept(asi)
        space = asi.peek()
        return space
    }

    fun evaluateExpression(expression: Expression): T {
        val expressionEvaluator = AbstractExpressionEvaluator(space, lattice.operations)
        return expression.accept(expressionEvaluator)
    }
}

class AbstractStateInterpreter<T>(init: AState<T>, val lattice: AiLattice<T>) : AstVisitor<Unit>() {
    private val maxIterations = 10000

    val stack = LinkedList<AState<T>>()

    init {
        stack.push(init)
    }

    override fun defaultVisit(obj: Any) {}

    fun peek() = stack.peek()!!
    fun push(s: AState<T>) = stack.push(s)
    fun pop() = stack.pop()
    fun dup(): AState<T>? {
        val old = peek()
        push(HashMap())
        return old
    }

    fun replace(): AState<T>? {
        val s = pop()
        pop()
        push(s)
        return s
    }


    fun evaluateTrue(expr: Expression): Boolean {
        val v = evaluate(expr)
        return lattice.isTrueable(v)
    }

    fun evaluateFalse(expr: Expression): Boolean {
        val v = evaluate(expr)
        return lattice.isFalseable(v)
    }

    fun evaluate(expr: Expression): T {
        val eval = AbstractExpressionEvaluator(peek(), lattice.operations)
        return expr.accept(eval)
    }

    override fun visit(ifStatement: IfStatement) {
        val branchStates = LinkedList<AState<T>>()
        for ((cond, branch) in ifStatement.conditionalBranches) {
            if (evaluateTrue(cond)) {
                dup();
                branch.accept(this)
                branchStates += pop();
            }
        }
        if (ifStatement.elseBranch.isNotEmpty()) {
            dup();
            ifStatement.elseBranch.accept(this)
            branchStates += pop();
        }

        val variables = branchStates.groupByVariables()
        for (variable in variables) {
            peek()[variable.key] = variable.value.reduce(lattice::branchReducer)
        }
    }

    override fun visit(caseStatement: CaseStatement) {
        TODO()
    }

    override fun visit(forStatement: ForStatement) {
        //TODO Maybe variable renaming!
        val initialAssignment = forStatement.variable.assignTo(forStatement.start)
        val v = SymbolicReference(forStatement.variable)
        val cond = v.le(forStatement.stop)
        val incr = v.plus(forStatement.step ?: IntegerLit(INT, 1.toBigInteger()))
        val incrAssign = forStatement.variable.assignTo(incr)

        var iter = 0
        initialAssignment.accept(this)
        while (evaluateTrue(cond) && iter < maxIterations) {
            val old = HashMap(peek())
            forStatement.statements.accept(this)
            incrAssign.accept(this)
            val new = peek()
            if (lattice.stateEquals(old, new)) break //Fixpoint reached
            iter++;
        }
    }

    override fun visit(whileStatement: WhileStatement) {
        val cond = whileStatement.condition
        var iter = 0
        while (evaluateTrue(cond) && iter < maxIterations) {
            val old = HashMap(peek())
            whileStatement.statements.accept(this)
            val new = peek()
            if (lattice.stateEquals(old, new)) break //Fixpoint reached
            iter++
        }
    }

    override fun visit(repeatStatement: RepeatStatement) {
        var iter = 0
        val cond = repeatStatement.condition
        do {
            val old = HashMap(peek())
            repeatStatement.statements.accept(this)
            val new = peek()
            if (lattice.stateEquals(old, new)) break //Fixpoint reached
            iter++
        } while (!evaluateFalse(cond) && iter < maxIterations) //TODO test what is correct here
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        //TODO allow sub references, arrays?
        peek()[assignmentStatement.location.identifier] = evaluate(assignmentStatement.expression)
    }

    override fun visit(returnStatement: ReturnStatement) {
        //throw LoopAbortException()
    }

    override fun visit(exitStatement: ExitStatement) {
        //throw BodyAbortException()
    }
}

private class LoopAbortException : Throwable()
private class BodyAbortException : Throwable()

private fun <T> Collection<AState<T>>.groupByVariables(): Map<String, List<T>> {
    val seq = HashMap<String, MutableList<T>>()
    for (a in this) {
        for ((k, v) in a) {
            if (k !in seq) {
                seq[k] = LinkedList()
            }
            seq[k]?.add(v)
        }
    }
    return seq
}

class AbstractExpressionEvaluator<T>(val state: AState<T>,
                                     val operator: AbstractOperations<T>) : AstVisitor<T>() {
    override fun defaultVisit(obj: Any): T {
        TODO("${obj.javaClass} is not covered")
    }

    override fun visit(binaryExpression: BinaryExpression): T {
        val (left, op, right) = binaryExpression
        val leftValue = left.accept(this)
        val rightValue = right.accept(this)

        return when (op) {
            Operators.ADD -> operator.add(leftValue, rightValue)
            Operators.SUB -> operator.sub(leftValue, rightValue)
            Operators.DIV -> operator.div(leftValue, rightValue)
            Operators.MULT -> operator.mult(leftValue, rightValue)
            Operators.POWER -> operator.power(leftValue, rightValue)

            Operators.AND -> operator.and(leftValue, rightValue)
            Operators.OR -> operator.or(leftValue, rightValue)
            Operators.XOR -> operator.xor(leftValue, rightValue)

            Operators.EQUALS -> operator.equals(leftValue, rightValue)
            Operators.NOT_EQUALS -> operator.notEquals(leftValue, rightValue)

            Operators.GREATER_EQUALS -> operator.ge(leftValue, rightValue)
            Operators.GREATER_THAN -> operator.gt(leftValue, rightValue)
            Operators.LESS_EQUALS -> operator.le(leftValue, rightValue)
            Operators.LESS_THAN -> operator.lt(leftValue, rightValue)

            else -> TODO("$op not covered")
        }
    }

    override fun visit(unaryExpression: UnaryExpression): T {
        val (op, right) = unaryExpression
        val rightValue = right.accept(this)

        return when (op) {
            Operators.NOT -> operator.not(rightValue)
            Operators.MINUS -> operator.minus(rightValue)
            else -> TODO("$op not covered")
        }
    }

    override fun visit(literal: Literal): T {
        return operator.literal(literal)
    }

    override fun visit(symbolicReference: SymbolicReference): T {
        //TODO sub identifier, and arrays
        return state[symbolicReference.identifier]
                ?: operator.emptyElement()
    }

    override fun visit(invocation: Invocation): T {
        val parameters = invocation.inputParameters.map { it.expression.accept(this) }
        val dt = invocation.invoked.returnType
        return operator.invocation(invocation.calleeName,
                dt, parameters);
    }
}

interface AbstractOperations<T> {
    fun add(leftValue: T, rightValue: T): T
    fun sub(leftValue: T, rightValue: T): T
    fun div(leftValue: T, rightValue: T): T
    fun mult(leftValue: T, rightValue: T): T
    fun power(leftValue: T, rightValue: T): T
    fun and(leftValue: T, rightValue: T): T
    fun or(leftValue: T, rightValue: T): T
    fun xor(leftValue: T, rightValue: T): T
    fun gt(leftValue: T, rightValue: T): T
    fun lt(leftValue: T, rightValue: T): T
    fun ge(leftValue: T, rightValue: T): T
    fun le(leftValue: T, rightValue: T): T
    fun equals(leftValue: T, rightValue: T): T
    fun notEquals(leftValue: T, rightValue: T): T
    fun literal(literal: Literal): T
    fun not(rightValue: T): T
    fun minus(rightValue: T): T
    fun emptyElement(): T
    fun invocation(calleeName: String, dt: AnyDt?, parameters: List<T>): T
}

/**
 * see https://de.wikipedia.org/wiki/Intervallarithmetik#Grundrechenarten
 */
class IntOperations : AbstractOperations<IntervalSet> {
    private val INTERVAL_FALSE = Interval(0, 0)
    private val INTERVAL_TRUE = Interval(1, 1)
    private val INTERVAL_ALL = Interval(0, 1)

    override fun add(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue, Interval::plus)
    }

    fun combine(a: IntervalSet, b: IntervalSet, op: (Interval, Interval) -> Interval): IntervalSet {
        val s = IntervalSet()
        a.intervals.forEach { li ->
            b.intervals.forEach { ri ->
                val i = op(li, ri)
                s.add(i.a, i.b)
            }
        }
        return s
    }

    override fun sub(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue, Interval::minus)
    }

    override fun div(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue, Interval::div)
    }

    override fun mult(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue, Interval::times)
    }

    override fun power(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue, Interval::power)
    }

    override fun and(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combineBoolean(leftValue, rightValue) { a, b -> a and b }
    }

    private fun combineBoolean(left: IntervalSet, right: IntervalSet, f: (Boolean, Boolean) -> Boolean): IntervalSet {
        val s = IntervalSet()
        if (0 in left && 0 in right) {
            s.add(if (f(false, false)) 1 else 0)
        }
        if (1 in left && 0 in right) {
            s.add(if (f(true, false)) 1 else 0)
        }
        if (1 in left && 1 in right) {
            s.add(if (f(true, true)) 1 else 0)
        }
        if (0 in left && 1 in right) {
            s.add(if (f(false, true)) 1 else 0)
        }
        return s
    }

    override fun or(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combineBoolean(leftValue, rightValue) { a, b -> a or b }
    }

    override fun xor(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combineBoolean(leftValue, rightValue) { a, b -> a xor b }
    }

    override fun gt(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { l, r ->
            when {
                l.a > r.b -> INTERVAL_TRUE
                l.b <= r.b -> INTERVAL_FALSE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun lt(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { l, r ->
            when {
                l.b < r.a -> INTERVAL_TRUE
                l.a >= r.b -> INTERVAL_FALSE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun ge(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { l, r ->
            when {
                l.a >= r.b -> INTERVAL_TRUE
                l.b < r.b -> INTERVAL_FALSE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun le(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { l, r ->
            when {
                l.b <= r.a -> INTERVAL_TRUE
                l.a > r.b -> INTERVAL_FALSE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun equals(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { a, b ->
            when {
                a.disjoint(b) -> INTERVAL_FALSE
                a == b -> INTERVAL_TRUE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun notEquals(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet {
        return combine(leftValue, rightValue) { a, b ->
            when {
                a.disjoint(b) -> INTERVAL_TRUE
                a == b -> INTERVAL_FALSE
                else -> INTERVAL_ALL
            }
        }
    }

    override fun literal(literal: Literal): IntervalSet {
        val s = emptyElement()
        when (literal) {
            is IntegerLit -> s.add(literal.value.toInt())
            is StringLit -> {
                Console.info("AI: ${literal.value.hashCode()} is for ${literal.value}")
                s.add(literal.value.hashCode())
            }
            is RealLit -> {
                val d = literal.value.toDouble()
                s.add(floor(d).toInt(), ceil(d).toInt())
            }
            is EnumLit -> s.add(literal.dataType.obj?.get(literal.value)!!)
            is NullLit -> s.add(0)
            is BooleanLit -> s.add(if (literal.value) 1 else 0)
            is BitLit -> s.add(literal.value.toInt())

            is ToDLit -> TODO()
            is DateLit -> TODO()
            is TimeLit -> TODO()
            is DateAndTimeLit -> TODO()
            is UnindentifiedLit -> TODO()
        }
        return s
    }

    override fun not(rightValue: IntervalSet): IntervalSet {
        val s = emptyElement()
        if (0 in rightValue) s.add(1)
        if (1 in rightValue) s.add(0)
        return s
    }

    override fun minus(rightValue: IntervalSet): IntervalSet {
        val s = emptyElement()
        rightValue.intervals.forEach { i ->
            s.add(-i.b, -i.a)
        }
        return s
    }

    override fun emptyElement(): IntervalSet = IntervalSet()

    override fun invocation(calleeName: String, dt: AnyDt?, parameters: List<IntervalSet>): IntervalSet {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}

private operator fun Interval.plus(ri: Interval): Interval {
    return Interval(a + ri.a, b + ri.b)
}

private operator fun Interval.minus(ri: Interval): Interval {
    return Interval(a - ri.b, b - ri.a)
}

private operator fun Interval.times(ri: Interval): Interval {
    //[x_1, x_2] \cdot [y_1, y_2] = [\min(x_1 y_1,x_1 y_2,x_2 y_1,x_2 y_2), \max(x_1 y_1,x_1 y_2,x_2 y_1,x_2 y_2)]
    val s = listOf(a * ri.a, a * ri.b, b * ri.a, b * ri.b)
    return Interval(s.min()!!, s.max()!!)
}


private fun Interval.power(ri: Interval): Interval {
    val s = listOf(a.pow(ri.a), a.pow(ri.b), b.pow(ri.a), b.pow(ri.b))
    return Interval(floor(s.min()!!).toInt(), ceil(s.max()!!).toInt())
}

private fun Int.pow(a: Int): Double = Math.pow(this.toDouble(), a.toDouble())

private operator fun Interval.div(ri: Interval): Interval {
    if (0 in ri) {
        //TODO Division by zero possible
    }
    val x = 1.0 / ri.b
    val y = 1.0 / ri.a
    val s = listOf(a * x, a * y, b * x, b * y)
    val mi = floor(s.min()!!).toInt()
    val ma = ceil(s.max()!!).toInt()
    return Interval(mi, ma)
}

private operator fun Interval.contains(i: Int): Boolean {
    return a <= i && i <= b;
}

class IntLattice : AiLattice<IntervalSet> {
    override val operations = IntOperations()

    override fun branchReducer(a: IntervalSet, b: IntervalSet): IntervalSet {
        val s = IntervalSet()
        s.addAll(a)
        s.addAll(b)
        return s
    }

    override fun isAlwaysTrue(t: IntervalSet) = 1 in t && t.size() == 1
    override fun isAlwaysFalse(t: IntervalSet) = 0 in t && t.size() == 1
    override fun isTrueable(t: IntervalSet) = 1 in t
    override fun isFalseable(t: IntervalSet) = 0 in t

    override fun stateEquals(a: AState<IntervalSet>, b: AState<IntervalSet>): Boolean {
        return a == b
    }
}

/*sealed class IntTree {
    abstract val lower: Int
    abstract val upper: Int

    data class Leave(val l: Int, val u: Int) : IntTree() {
        override val lower: Int
            get() = l
        override val upper: Int
            get() = u
    }

    data class Node(val left: IntTree, val right: IntTree) : IntTree() {
        override val lower: Int
            get() = left.lower
        override val upper: Int
            get() = right.upper
    }
}
*/
