package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.rvt.ModuleBuilder
import edu.kit.iti.formal.automation.rvt.SymbolicExecutioner
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.smv.ast.SMVModule
import java.io.File
import java.math.BigInteger

val TYPE_COUNTER = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.LOCAL
val TYPE_INPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.OUTPUT
val TYPE_OUTPUT_FUNCTION_BLOCK = VariableDeclaration.FLAG_COUNTER.get() or VariableDeclaration.INPUT


fun createProgramWithAbstraction(a: Frame, abstractedInvocation: List<BlockStatement>) = rewriteInvocation(a, abstractedInvocation)

fun evaluateFrameWithAbstraction(exec: Frame, abstractedBlocks: List<BlockStatement>): SMVModule {
    //val elements = exec.scope.getVisiblePous()
    val abstracted =
            if (abstractedBlocks.isEmpty()) exec.block
            else createProgramWithAbstraction(exec, abstractedBlocks)

    //IEC61131Facade.resolveDataTypes(PouElements(elements.toMutableList()), exec.scope.topLevel)

    File("${exec.block.name}_abstracted.st").bufferedWriter()
            .use { IEC61131Facade.printTo(it, abstracted, true) }

    val se = SymbolicExecutioner(exec.scope.topLevel)
    exec.block.accept(se)

    val moduleBuilder = ModuleBuilder(exec.block.name, exec.scope, se.peek())
    moduleBuilder.run()
    return moduleBuilder.module
}

fun rewriteInvocation(a: Frame, abstractedInvocation: List<BlockStatement>): BlockStatement {
    var new = a.block.clone()
    val scope = a.scope.copy()

    // foreach reference create a call counter
    abstractedInvocation.distinctBy { it.fqName }.forEach {
        val prefix = it.fqName.replace('.', '$')
        val sr = SymbolicReference(prefix + "_ccnt")
        new.statements.add(0, AssignmentStatement(sr, IntegerLit(INT, BigInteger.ZERO)))

        val vd = VariableDeclaration(sr.identifier, TYPE_COUNTER, UINT)
        scope.add(vd)
    }

    abstractedInvocation.forEach {
        val prefix = it.fqName.replace('.', '$')
        val rewriter = InvocationRewriter(prefix, scope, it)
        new.statements = new.statements.accept(rewriter) as StatementList
    }
    return new
}

class InvocationRewriter(val prefix: String,
                         val scope: Scope,
                         val toBeReplaced: BlockStatement) : AstMutableVisitor() {
    override fun visit(blockStatement: BlockStatement): Any {
        if (blockStatement != toBeReplaced) return super.visit(blockStatement)
        val list = StatementList()

        val cnt = SymbolicReference(prefix + "_ccnt")
        val counterIncr = AssignmentStatement(cnt, cnt plus IntegerLit(UINT, BigInteger.ONE))

        list += counterIncr

        //Inputs
        val prefix = blockStatement.repr().replace('.', '$')
        val inputsAssign =
                blockStatement.input.map {
                    val n = "$prefix$${it.identifier}"
                    val vdOut = scope.getVariable(it)
                    val inputName = "${n}__input"
                    scope.add(VariableDeclaration(inputName, 0 or TYPE_INPUT_FUNCTION_BLOCK, vdOut.dataType!!))
                    inputName assignTo n
                }

        val randomOutput = blockStatement.output.map {
            val n = "$prefix$${it.identifier}"
            val vdOut = scope.getVariable(it)
            val inputName = "${n}__random"
            scope.add(VariableDeclaration(inputName, 0 or TYPE_OUTPUT_FUNCTION_BLOCK, vdOut.dataType!!))
            n assignTo inputName
        }
        list.addAll(inputsAssign)
        list.addAll(randomOutput)

        //TODO remove state

        return list
    }
}
