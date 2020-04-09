package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.st.ast.Invocation
import edu.kit.iti.formal.automation.st.ast.InvocationStatement
import edu.kit.iti.formal.automation.st.ast.Top
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.util.concurrent.Callable


abstract class Task : Callable<Boolean> {
    abstract override fun call(): Boolean
}

abstract class NamedTask(val name: String) : Callable<Boolean> {
    abstract override fun call(): Boolean
}

class AllTask(vararg val sub: Task) : Task() {
    override fun call(): Boolean = sub.all { it.call() }
}

class AnyTask(vararg val sub: Task) : Task() {
    override fun call(): Boolean = sub.any { it.call() }
}

class NotTask(val sub: Task) : Task() {
    override fun call(): Boolean = !sub.call()
}


infix fun Task.and(other: Task) = AllTask(this, other)
infix fun Task.or(other: Task) = AnyTask(this, other)
fun Task.not(): Task = NotTask(this)


/**
 *
 * @author Alexander Weigl
 * @version 1 (15.07.18)
 */
//
class SearchForInvocation : AstVisitor<Unit>() {
    var foundInvocation = false
    override fun defaultVisit(obj: Any) {}
    override fun visit(invocation: Invocation) {
        foundInvocation = true
    }

    override fun visit(invocation: InvocationStatement) {
        foundInvocation = true
    }
}

fun Top.containsInvocations(): Boolean {
    val sfi = SearchForInvocation()
    this.accept(sfi)
    return sfi.foundInvocation
}
//
