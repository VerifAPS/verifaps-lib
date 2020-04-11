package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.st.ast.InvocationStatement
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.util.error
import java.util.*
import kotlin.collections.HashMap

typealias CallSiteMapping = List<Pair<CallSite, CallSite>>

class ModularProgram(val filename: String) {
    fun findCallSite(aa: String): CallSite {
        return callSites.find { it.repr() == aa } ?: throw IllegalArgumentException("could not find $aa")
    }

    val elements: PouElements by lazy { readProgramsOrError(filename) }

    val entry: ProgramDeclaration by lazy {
        elements.findFirstProgram() ?: kotlin.error("Could not find any PROGRAM in $filename")
    }

    val callSites: List<CallSite> by lazy {
        CallSiteFinder(entry).run()
    }
}

/**
 * Global Identificator of a function block call
 */
data class CallSite(val vars: List<String>, val number: Int, val statement: InvocationStatement) {

    val inferedContext = HashMap<String, SMVExpr>()
    var specifiedContext : SMVExpr? = null

    fun repr(): String = vars.joinToString(".") + ".$number"
    fun correspond(other: CallSite) =
            vars.subList(1, vars.lastIndex) == other.vars.subList(1, other.vars.lastIndex)
                    && other.number == number

    fun isPrefix(ids: List<String>) = ids.size <= vars.size && ids.zip(vars).all { (a, b) -> a == b }
}

data class CallSiteContext(val vars: Stack<String> = Stack(),
                           var invocationCounter: Stack<MutableMap<String, Int>> = Stack()) {
    fun endCall() {
        vars.pop()
        invocationCounter.pop()
    }

    fun startCall(c: InvocationStatement): CallSite {
        vars.push(c.callee.identifier)
        val currentNo = invocationCounter.peek().computeIfAbsent(c.callee.identifier) { 0 }
        val cs = CallSite(vars.toList(), currentNo, c)
        invocationCounter.peek().put(c.callee.identifier, 1 + currentNo)
        invocationCounter.push(hashMapOf())
        return cs
    }
}

class CallSiteFinder(val entry: ProgramDeclaration) {
    val callSites: MutableList<CallSite> = arrayListOf()
    val context = CallSiteContext()

    init {
        context.vars += entry.name
        context.invocationCounter.push(hashMapOf())
    }

    fun run(): List<CallSite> {
        entry.accept(CallSiteFinderSearcher())
        return callSites
    }

    inner class CallSiteFinderSearcher : AstVisitorWithScope<Unit>() {
        override fun defaultVisit(obj: Any) {}
        override fun visit(invocation: InvocationStatement) {
            val ctx = context.startCall(invocation)
            invocation.setMetadata(ctx.javaClass, ctx)
            callSites += ctx
            val vd = scope.resolveVariable(invocation.callee)
            if (vd != null) {
                try {
                    val fbd = (vd.dataType as FunctionBlockDataType).functionBlock
                    fbd.accept(this)
                } catch (e: IllegalStateException) {
                    error("Could not find the function block for call" +
                            " ${invocation.ruleContext?.text} in " +
                            " line ${invocation.startPosition.lineNumber}")
                }
            }
            context.endCall()
        }
    }
}
