package edu.kit.iti.formal.automation.st.ast

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.INT
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.06.19)
 */

//Helpers
fun <T : Expression> Iterable<T>.disjunction() = reduce { a: Expression, b: Expression -> a or b }

fun <T : Expression> Iterable<T>.conjunction() = reduce { a: Expression, b: Expression -> a and b }
fun <T : Expression> Iterable<T>.sum() = reduce { a: Expression, b: Expression -> a plus b }
fun <T : Expression> Iterable<T>.substract() = reduce { a: Expression, b: Expression -> a minus b }
fun <T : Expression> Iterable<T>.product() = reduce { a: Expression, b: Expression -> a times b }
fun <T : Expression> Iterable<T>.division() = reduce { a: Expression, b: Expression -> a div b }
//endregion


/**
 * Get the return type of an invocation.
 */
val Invoked?.returnType: AnyDt?
    get() {
        return when (this) {
            is Invoked.Program -> null
            is Invoked.FunctionBlock -> null
            is Invoked.Function -> function.returnType.obj
            is Invoked.Method -> method.returnType.obj
            is Invoked.Action -> null
            null -> null
        }
    }


/**
 * Creates an array access expression
 */
operator fun SymbolicReference.get(it: Iterable<Int>): SymbolicReference {
    val exprs = it.map { IntegerLit(INT, it.toBigInteger()) }
    return this.copy(subscripts = ExpressionList(exprs.toMutableList()))
}


operator fun SymbolicReference.get(fieldName: String): SymbolicReference = copy(sub = SymbolicReference(fieldName))
operator fun SymbolicReference.get(it: IntArray) = this[it.toList()]

infix fun SymbolicReference.assignTo(init: Expression?) = AssignmentStatement(this, init!!)

infix fun String.assignTo(expr: Expression) = AssignmentStatement(SymbolicReference(this), expr)

infix fun String.assignTo(expr: String) =
        AssignmentStatement(SymbolicReference(this), SymbolicReference(expr))

//region oo
val InterfaceDeclaration.definedMethods: List<Pair<HasMethods, MethodDeclaration>>
    get() {
        val seq = arrayListOf<Pair<HasMethods, MethodDeclaration>>()
        for (iface in allInterfaces) {
            for (it in iface.methods)
                seq.add(iface to it)
        }
        return seq
    }

infix fun MethodDeclaration.sameSignature(other: MethodDeclaration): Boolean {
    if (name != other.name)
        return false

    val input1 = scope.variables.filter { it.isInput }
    val input2 = scope.variables.filter { it.isInput }

    for (v1 in input1) {
        val v2 = input2.find { it.name == v1.name } ?: return false
        if (v2.dataType != v1.dataType) return false
    }

    for (v2 in input2) {
        val v1 = input1.find { it.name == v2.name } ?: return false
        if (v2.dataType != v1.dataType) return false
    }
    return true
}

infix fun MethodDeclaration.isCompatibleTo(parent: MethodDeclaration): Boolean {
    if (name != parent.name) return false // equal name

    //return type
    if (returnType.obj!!.isAssignableTo(parent.returnType.obj!!)) {
        return false
    }

    val params = scope.variables.filter { it.isInput }.zip(scope.variables.filter { it.isInput })
    return params.all { (p1, p2) ->
        p2.dataType!!.isAssignableTo(p1.dataType!!)
    }
}

/**
 *
 */
val ClassDeclaration.declaredMethods: Collection<Pair<HasMethods, MethodDeclaration>>
    get() {
        val seq = LinkedList(definedMethods)
        for (iface in allInterfaces) {
            for (it in iface.methods)
                seq.add(iface to it)
        }
        return seq
    }

/**
 * returns defined methods (methods with a body) of this class and parent classes.
 */
val ClassDeclaration.definedMethods: Collection<Pair<HasMethods, MethodDeclaration>>
    get() {
        val seq = arrayListOf<Pair<HasMethods, MethodDeclaration>>()
        for (iface in parents) {
            for (it in iface.methods)
                seq.add(iface to it)
        }
        return seq
    }

val ClassDeclaration.parents: List<ClassDeclaration>
    get() {
        var c = parent.obj
        val seq = arrayListOf<ClassDeclaration>()
        while (c != null) {
            seq.add(c)
            c = parent.obj;
            if (c in seq) break
        }
        return seq
    }

val ClassDeclaration.allInterfaces: List<InterfaceDeclaration>
    get() {
        val seq = arrayListOf<InterfaceDeclaration>()
        interfaces.forEach { it.obj?.let { seq.add(it); seq.addAll(it.allInterfaces) } }
        parents.forEach { c ->
            c.interfaces.forEach { it.obj?.let { seq.add(it); seq.addAll(it.allInterfaces) } }
        }
        return seq
    }

val InterfaceDeclaration.allInterfaces: List<InterfaceDeclaration>
    get() {
        val seq = arrayListOf<InterfaceDeclaration>()
        interfaces.forEach {
            it.obj?.let { seq.add(it); seq.addAll(it.allInterfaces) }
        }
        return seq
    }
//endregion