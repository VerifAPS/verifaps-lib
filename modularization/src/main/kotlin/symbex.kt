package edu.kit.iti.formal.automation.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.smv.ast.SMVModule
import java.io.File
import java.math.BigInteger

val TYPE_COUNTER = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.LOCAL
val TYPE_INPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.OUTPUT
val TYPE_OUTPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.INPUT


fun createProgramWithAbstraction(a: PouExecutable, abstractedInvocation: List<CallSite>)
        = rewriteInvocation(a, abstractedInvocation)

fun evaluateProgramWithAbstraction(exec: PouExecutable, abstractedInvocation: List<CallSite>): SMVModule {
    val elements = exec.scope.getVisiblePous()

    val abstracted =
            if (abstractedInvocation.isEmpty()) exec
            else createProgramWithAbstraction(exec, abstractedInvocation)

    IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)

    File("${exec.name}_abstracted.st").bufferedWriter()
            .use { IEC61131Facade.printTo(it, abstracted, true) }

    val simplified = SymbExFacade.simplify(exec)

    File("${exec.name}_simplified.st").bufferedWriter()
            .use { IEC61131Facade.printTo(it, simplified, true) }

    val se = SymbolicExecutioner(exec.scope.topLevel)
    simplified.accept(se)

    val moduleBuilder = ModuleBuilder(exec, se.peek())
    moduleBuilder.run()
    return moduleBuilder.module
}

fun rewriteInvocation(a: PouExecutable, abstractedInvocation: List<CallSite>): PouExecutable {
    val new = a.setAllMetadata()

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
        new.stBody = new.stBody!!.accept(rewriter) as StatementList
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
            val list = StatementList()
            val assignments = invocation.inputParameters.map {
                val a = invocation.callee.setAllMetadata()
                a.sub = SymbolicReference(it.name!!)
                AssignmentStatement(a, it.expression)
            }
            list.addAll(assignments)

            val inputVariables =
                    (toBeReplaced.invoked as Invoked.FunctionBlock).fb.scope.variables
                            .filter { it.isInput }

            val outputVariables =
                    (toBeReplaced.invoked as Invoked.FunctionBlock).fb.scope.variables
                            .filter { it.isOutput }

            val cnt = SymbolicReference(prefix + "_ccnt")
            val counterIncr = AssignmentStatement(cnt, cnt plus IntegerLit(UINT, BigInteger.ONE))

            list += counterIncr

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
            list.addAll(inputsAssign)
            list.addAll(randomOutput)
            return list
        } else {
            return invocation
        }
    }

}
