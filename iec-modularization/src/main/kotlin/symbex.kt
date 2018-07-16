package edu.kit.iti.formal.automation.modularization

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.smv.ast.SMVModule
import java.math.BigInteger

fun createProgramWithAbstraction(a: PouExecutable, abstractedInvocation: List<CallSite>) = rewriteInvocation(a, abstractedInvocation)

fun evaluateProgramWithAbstraction(a: PouExecutable, abstractedInvocation: List<CallSite>): SMVModule {
    val sym = SymbExFacade.evaluateProgram(a)
    //TODO optimize
    return sym
}

fun rewriteInvocation(a: PouExecutable, abstractedInvocation: List<CallSite>): PouExecutable {
    val new = a.clone()

    // foreach reference create a call counter
    abstractedInvocation.distinctBy { it.vars }.forEach {
        val prefix = it.vars.joinToString("$")
        val sr = SymbolicReference(prefix + "_ccnt")
        new.stBody!!.add(0, AssignmentStatement(sr, IntegerLit(INT, BigInteger.ZERO)))

        val vd = VariableDeclaration(sr.identifier, TYPE_COUNTER,
                SimpleTypeDeclaration(
                        baseType = RefTo(UINT),
                        initialization = IntegerLit(INT, BigInteger.ZERO)))
        new.scope.add(vd)
    }

    abstractedInvocation.forEach {
        val prefix = it.vars.joinToString("$")
        val rewriter = InvocationRewriter(prefix, new.scope, it)
        new.stBody!!.accept(rewriter)
    }
    return new
}

class InvocationRewriter(val prefix: String, val scope: Scope, val callSite: CallSite) : AstMutableVisitor() {
    val toBeReplaced: InvocationStatement = callSite.statement

    /*override fun visit(assignmentStatement: AssignmentStatement): Statement {
        val loc = assignmentStatement.location as SymbolicReference
        if (loc.identifier == loc.identifier) {
            return StatementList() // delete all assignment to the function block
        }
        return assignmentStatement
    }*/

    override fun visit(invocation: InvocationStatement): Statement {
        if (invocation == toBeReplaced) {
            val assignments = invocation.inputParameters.map {
                val a = invocation.callee.clone()
                a.sub = SymbolicReference(it.name!!)
                AssignmentStatement(a, it.expression)
            }


            val inputVariables =
                    (toBeReplaced.invoked as Invoked.FunctionBlock).fb.scope.variables
                            .filter { it.isInput }

            val outputVariables =
                    (toBeReplaced.invoked as Invoked.FunctionBlock).fb.scope.variables
                            .filter { it.isOutput }

            val cnt = SymbolicReference(prefix + "_ccnt")
            val counterIncr = AssignmentStatement(cnt, cnt + IntegerLit(UINT, BigInteger.ONE))

            //Inputs
            val inputsAssign =
                    inputVariables.map {
                        val name = "$prefix\$${callSite.number}_${it.name}"
                        val fbV = SymbolicReference(invocation.callee.identifier,
                                SymbolicReference(it.name))
                        scope.add(VariableDeclaration(name, 0 or TYPE_INPUT_FUNCTION_BLOCK, it.typeDeclaration))
                        AssignmentStatement(SymbolicReference(name), fbV)
                    }

            val randomOutput = outputVariables.map {
                val name = "$prefix\$${callSite.number}_${it.name}"
                val fbV = SymbolicReference(invocation.callee.identifier, SymbolicReference(it.name))
                scope.add(VariableDeclaration(name, 0 or TYPE_OUTPUT_FUNCTION_BLOCK, it.typeDeclaration))
                AssignmentStatement(fbV, SymbolicReference(name))
            }

            return StatementList(assignments + listOf(counterIncr) + inputsAssign + randomOutput)
        } else {
            return invocation
        }
    }

}

val TYPE_COUNTER = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.LOCAL
val TYPE_INPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.OUTPUT
val TYPE_OUTPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.INPUT
