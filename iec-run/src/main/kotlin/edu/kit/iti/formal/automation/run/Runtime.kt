package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import java.util.*

/**
 * Represents the Runtime of ST-execution
 * changes the [state] depending on the visited Nodes
 */
class Runtime(val state: State) : DefaultVisitor<Unit>() {
    /*
     * stores the variable definitions (e.g. "VAR a : INT END_VAR"
     * The variables are scoped, hence the Stack data-type
     */
    private val definitionScopeStack: Stack<LocalScope> = Stack()
    private val typeDeclarationAdder = TypeDeclarationAdder()
    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.init
        return super.visit(variableDeclaration)
    }
    override fun defaultVisit(visitable: Visitable?)  {
        TODO("method not implemented for: $visitable")
    }

    override fun visit(typeDeclarations: TypeDeclarations?) {
        typeDeclarations?.forEach { (it as Visitable).accept<Unit>(this) }
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        typeDeclarationAdder.queueDeclaration(enumerationTypeDeclaration)
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        val localScope = programDeclaration.localScope
        definitionScopeStack.push(localScope)
        typeDeclarationAdder.addQueuedDeclarations(localScope.globalScope)
        initializeLocalVariables(localScope)

        return programDeclaration!!.programBody.accept(this)
    }

    private fun initializeLocalVariables(localScope: LocalScope) {
        val localVariables: Map<out String, VariableDeclaration> = localScope.localVariables
        localVariables.map {
            val initExpr = it.value.init
            val initialValue : Optional<ExpressionValue> = when(initExpr) {
                null -> Optional.empty()
                else -> Optional.of(initExpr.accept<ExpressionValue>(
                        ExpressionVisitor(state, definitionScopeStack.peek())
                ) as ExpressionValue)
            }

            state.put(it.key, initialValue)
        }
    }

    private fun chooseGuardedStatement(ifStatement: IfStatement) : GuardedStatement? {
        for (statement in ifStatement.conditionalBranches) {
            val returnValue : ExpressionValue = (statement.condition as Visitable)
                    .accept<ExpressionValue>(
                            ExpressionVisitor(state, definitionScopeStack.peek())
                    )
            if (returnValue.value is Boolean) {
                if (returnValue.value == true) {
                    return statement
                }
                //if returnValue is false -> continue to search with the next guarded statement
            } else {
                throw TypeMissmatchException("condition for if statement must be a boolean")
            }
        }
        return null
    }

    override fun visit(ifStatement: IfStatement) {
        val chosenCodeBlock = chooseGuardedStatement(ifStatement) ?: return
        chosenCodeBlock.accept<Any>(this) // will run visit(GuardedStatement)
    }

    override fun visit(guardedStatement: GuardedStatement) {
        guardedStatement.statements.accept(this)
    }

    override fun visit(statements: StatementList?) {
        statements!!.forEach { it.accept<Any>(this) }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        val expressionVisitor = ExpressionVisitor(state, definitionScopeStack.peek())
        val expressionValue = assignmentStatement.expression.accept<ExpressionValue>(expressionVisitor) as ExpressionValue
        val nodeName = assignmentStatement.location.accept<Any>(object : DefaultVisitor<Unit>() {
            override fun visit(symbolicReference: SymbolicReference) {
                state.updateValue(symbolicReference.identifier, expressionValue)
                println(symbolicReference.identifier)
            }

            override fun visit(deref: Deref) {
                TODO("implement")
            }
        })
        println(state)

    }
}