/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.MultiDimArrayValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.util.info
import org.antlr.v4.runtime.misc.Interval
import org.antlr.v4.runtime.misc.IntervalSet
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import kotlin.collections.HashMap
import kotlin.math.ceil
import kotlin.math.floor

/**
 * An abstract type is a mapping of a variable name to a an element of the lattice.
 */
typealias AState<T> = HashMap<String, T>

/**
 * An lattice is defined as several operations needed on the elements of the lattice.
 */
@Suppress("ktlint:standard:property-naming")
interface AiLattice<T> {
    fun branchReducer(a: T, b: T): T
    fun isAlwaysTrue(t: T): Boolean
    fun isAlwaysFalse(t: T): Boolean
    fun isTrueable(t: T): Boolean
    fun isFalseable(t: T): Boolean
    fun stateEquals(a: AState<T>, b: AState<T>): Boolean
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
    fun byDatatype(dataType: AnyDt): T
    fun declare(state: AState<T>, name: String, value: Value<AnyDt, Any>)
    fun havoc(state: AState<T>, name: String, dt: AnyDt)
}

/**
 * This class contains an API for abstract interpretation.
 * @author Alexander Weigl
 * @version 1 (06.11.19)
 */
class AbstractInterpretation<T>(val lattice: AiLattice<T>, val startSpace: AState<T>) {
    var space = startSpace

    /**
     * Initialize the scope, given by the default values of the datatype or initialisation.
     */
    fun interpret(scope: Scope) {
        for (variable in scope.variables) {
            lattice.declare(space, variable.name, (variable.initValue as Value<AnyDt, Any>))
        }
    }

    /**
     * Havoc the input and inout variables.
     */
    fun havocInputVariables(scope: Scope) {
        for (variable in scope.variables.filter { it.isInput || it.isInOut }) {
            lattice.havoc(space, variable.name, variable.dataType!!)
        }
    }

    fun interpretFixpoint(e: Top, scope: Scope? = null, havoc: Boolean = false): Map<String, T> {
        if (scope != null) interpret(scope)
        do {
            if (scope != null && havoc) havocInputVariables(scope)
            val oldSpace = HashMap(space)
            interpret(e)
            val newSpace = HashMap(space)

            println(oldSpace)
            println(newSpace)
        } while (!lattice.stateEquals(newSpace, oldSpace)) // TODO maybe projection on non-input variables?!
        return space
    }

    fun interpret(e: Top): AState<T> {
        val asi = AbstractStateInterpreter(space, lattice)
        e.accept(asi)
        space = asi.peek()
        return space
    }

    fun interpret(expression: Expression): T {
        val expressionEvaluator = AbstractExpressionEvaluator(space, lattice)
        return expression.accept(expressionEvaluator)
    }
}

class AbstractStateInterpreter<T>(init: AState<T>, val lattice: AiLattice<T>) : AstVisitor<Unit>() {
    private val maxIterations = 10000
    private val stack = LinkedList<AState<T>>()

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
        val eval = AbstractExpressionEvaluator(peek(), lattice)
        return expr.accept(eval)
    }

    override fun visit(ifStatement: IfStatement) {
        val branchStates = LinkedList<AState<T>>()
        for ((cond, branch) in ifStatement.conditionalBranches) {
            if (evaluateTrue(cond)) {
                dup()
                branch.accept(this)
                branchStates += pop()
            }
        }
        if (ifStatement.elseBranch.isNotEmpty()) {
            dup()
            ifStatement.elseBranch.accept(this)
            branchStates += pop()
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
        // TODO Maybe variable renaming!
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
            if (lattice.stateEquals(old, new)) break // Fixpoint reached
            iter++
        }
    }

    override fun visit(whileStatement: WhileStatement) {
        val cond = whileStatement.condition
        var iter = 0
        while (evaluateTrue(cond) && iter < maxIterations) {
            val old = HashMap(peek())
            whileStatement.statements.accept(this)
            val new = peek()
            if (lattice.stateEquals(old, new)) break // Fixpoint reached
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
            if (lattice.stateEquals(old, new)) break // Fixpoint reached
            iter++
        } while (!evaluateFalse(cond) && iter < maxIterations) // TODO test what is correct here
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        // TODO allow sub references, arrays?
        peek()[assignmentStatement.location.identifier] = evaluate(assignmentStatement.expression)
    }

    override fun visit(returnStatement: ReturnStatement) {
        // throw LoopAbortException()
    }

    override fun visit(exitStatement: ExitStatement) {
        // throw BodyAbortException()
    }
}

class AbstractExpressionEvaluator<T>(
    val state: AState<T>,
    val operator: AiLattice<T>,
) : AstVisitor<T>() {
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

    override fun visit(literal: Literal): T = operator.literal(literal)

    override fun visit(symbolicReference: SymbolicReference): T {
        // TODO sub identifier, and arrays
        return state[symbolicReference.identifier]
            ?: operator.emptyElement()
    }

    override fun visit(invocation: Invocation): T {
        val parameters = invocation.inputParameters.map { it.expression.accept(this) }
        val dt = invocation.invoked.returnType
        return operator.invocation(invocation.calleeName, dt, parameters)
    }
}

/**
 * see https://de.wikipedia.org/wiki/Intervallarithmetik#Grundrechenarten
 */
class IntLattice : AiLattice<IntervalSet> {
    override fun declare(state: AState<IntervalSet>, name: String, value: Value<AnyDt, Any>) {
        value.dataType.accept(object : DataTypeVisitorNN<Unit> {
            override fun defaultVisit(obj: Any) {}
            override fun visit(real: AnyReal) {
                val v = (value.value as BigDecimal).toDouble()
                state[name] = IntervalSet.of(floor(v).toInt(), floor(v).toInt())
            }

            override fun visit(anyInt: AnyInt) {
                val v = (value.value as BigInteger).toInt()
                state[name] = IntervalSet.of(v)
            }

            override fun visit(bool: AnyBit.BOOL) {
                val v = (value.value as Boolean)
                state[name] = IntervalSet.of(if (v) 1 else 0)
            }

            override fun visit(anyBit: AnyBit) {
                val v = (value.value as BigInteger).toInt()
                state[name] = IntervalSet.of(v)
            }

            override fun visit(arrayType: ArrayType) {
                val arrayInit = value.value as MultiDimArrayValue
                for (idx in arrayType.allIndices()) {
                    val n = idx.joinToString(",", "$name[", "]")
                    val value1 = arrayInit[idx]
                    declare(state, n, value1)
                }
            }

            override fun visit(recordType: RecordType) {
                for (idx in recordType.fields) {
                    val n = "$name.${idx.name}"
                    declare(state, n, idx.initValue as Value<AnyDt, Any>)
                }
            }
        })
    }

    override fun havoc(space: AState<IntervalSet>, name: String, dt: AnyDt) {
        dt.accept(object : DataTypeVisitorNN<Unit> {
            override fun defaultVisit(obj: Any) {}
            override fun visit(real: AnyReal) {
                space[name] = IntervalSet.of(Int.MIN_VALUE, Int.MAX_VALUE)
            }

            override fun visit(anyInt: AnyInt) {
                space[name] = IntervalSet.of(anyInt.lowerBound.toInt(), anyInt.upperBound.toInt())
            }

            override fun visit(bool: AnyBit.BOOL) {
                space[name] = IntervalSet.of(0, 1)
            }

            override fun visit(anyBit: AnyBit) {
                visit(AnyInt(anyBit.bitLength, false))
            }

            override fun visit(arrayType: ArrayType) {
                for (idx in arrayType.allIndices()) {
                    val n = idx.joinToString(",", "name[", "]")
                    havoc(space, n, arrayType.fieldType)
                }
            }

            override fun visit(recordType: RecordType) {
                for (idx in recordType.fields) {
                    val n = "$name.${idx.name}"
                    havoc(space, n, idx.dataType!!)
                }
            }
        })
    }

    private val INTERVAL_FALSE = Interval(0, 0)
    private val INTERVAL_TRUE = Interval(1, 1)
    private val INTERVAL_ALL = Interval(0, 1)

    override fun add(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue, Interval::plus)

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

    override fun sub(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue, Interval::minus)

    override fun div(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue, Interval::div)

    override fun mult(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue, Interval::times)

    override fun power(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue, Interval::power)

    override fun and(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combineBoolean(leftValue, rightValue) { a, b -> a and b }

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

    override fun or(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combineBoolean(leftValue, rightValue) { a, b -> a or b }

    override fun xor(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combineBoolean(leftValue, rightValue) { a, b -> a xor b }

    override fun gt(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { l, r ->
        when {
            l.a > r.b -> INTERVAL_TRUE
            l.b <= r.b -> INTERVAL_FALSE
            else -> INTERVAL_ALL
        }
    }

    override fun lt(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { l, r ->
        when {
            l.b < r.a -> INTERVAL_TRUE
            l.a >= r.b -> INTERVAL_FALSE
            else -> INTERVAL_ALL
        }
    }

    override fun ge(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { l, r ->
        when {
            l.a >= r.b -> INTERVAL_TRUE
            l.b < r.b -> INTERVAL_FALSE
            else -> INTERVAL_ALL
        }
    }

    override fun le(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { l, r ->
        when {
            l.b <= r.a -> INTERVAL_TRUE
            l.a > r.b -> INTERVAL_FALSE
            else -> INTERVAL_ALL
        }
    }

    override fun equals(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { a, b ->
        when {
            a.disjoint(b) -> INTERVAL_FALSE
            a == b -> INTERVAL_TRUE
            else -> INTERVAL_ALL
        }
    }

    override fun notEquals(leftValue: IntervalSet, rightValue: IntervalSet): IntervalSet = combine(leftValue, rightValue) { a, b ->
        when {
            a.disjoint(b) -> INTERVAL_TRUE
            a == b -> INTERVAL_FALSE
            else -> INTERVAL_ALL
        }
    }

    override fun literal(literal: Literal): IntervalSet {
        val s = emptyElement()
        when (literal) {
            is IntegerLit -> s.add(literal.value.toInt())
            is StringLit -> {
                info("AI: ${literal.value.hashCode()} is for ${literal.value}")
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

    override fun byDatatype(dataType: AnyDt): IntervalSet = dataType.accept(object : DataTypeVisitorNN<IntervalSet> {
        override fun defaultVisit(obj: Any) = IntervalSet(0)
        override fun visit(enumerateType: EnumerateType) = IntervalSet(enumerateType.get(enumerateType.defValue)!!)
    })

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
        TODO("not implemented") // To change body of created functions use File | Settings | File Templates.
    }

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
        if (a === b) return true
        if (a.keys != b.keys) return false
        return a.keys.all { k ->
            val x = a[k]
            val y = b[k]
            Objects.equals(x, y)
        }
    }
}

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

private operator fun Interval.plus(ri: Interval): Interval = Interval(a + ri.a, b + ri.b)

private operator fun Interval.minus(ri: Interval): Interval = Interval(a - ri.b, b - ri.a)

private operator fun Interval.times(ri: Interval): Interval {
    // [x_1, x_2] \cdot [y_1, y_2] = [\min(x_1 y_1,x_1 y_2,x_2 y_1,x_2 y_2), \max(x_1 y_1,x_1 y_2,x_2 y_1,x_2 y_2)]
    val s = listOf(a * ri.a, a * ri.b, b * ri.a, b * ri.b)
    return Interval(s.minOrNull()!!, s.maxOrNull()!!)
}

private fun Interval.power(ri: Interval): Interval {
    val s = listOf(a.pow(ri.a), a.pow(ri.b), b.pow(ri.a), b.pow(ri.b))
    return Interval(floor(s.minOrNull()!!).toInt(), ceil(s.maxOrNull()!!).toInt())
}

private fun Int.pow(a: Int): Double = Math.pow(this.toDouble(), a.toDouble())

private operator fun Interval.div(ri: Interval): Interval {
    if (0 in ri) {
        // TODO Division by zero possible
    }
    val x = 1.0 / ri.b
    val y = 1.0 / ri.a
    val s = listOf(a * x, a * y, b * x, b * y)
    val mi = floor(s.minOrNull()!!).toInt()
    val ma = ceil(s.maxOrNull()!!).toInt()
    return Interval(mi, ma)
}

private operator fun Interval.contains(i: Int): Boolean = a <= i && i <= b

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
