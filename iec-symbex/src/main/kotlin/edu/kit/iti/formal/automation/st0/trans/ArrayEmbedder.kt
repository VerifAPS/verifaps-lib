package edu.kit.iti.formal.automation.st0.trans

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st0.STSimplifier

/**
 * Created by weigl on 03/10/14.
 * @author Alexander Weigl, Augusto Modanese
 */
class ArrayEmbedder : ST0Transformation {
    private var state: STSimplifier.State? = null
    //private var instanceCount: Long = 0

    override fun transform(state: STSimplifier.State) {
        this.state = state
        state.theProgram!!.scope.variables
                .filter { it.typeDeclaration is ArrayTypeDeclaration }
                .forEach { arrayVariable ->
                    val (_, baseType, initialization, ranges) = (arrayVariable.typeDeclaration!! as ArrayTypeDeclaration)
                    assert(initialization != null)
                    for ((start, stop) in ranges) {
                        val rangeMin = Integer.parseInt(start.text)
                        val rangeMax = Integer.parseInt(stop.text)
                        // TODO multiple ranges
                        for (i in rangeMin..rangeMax) {
                            val init = initialization!!.initValues[i - rangeMin]
                            val `var` = VariableDeclaration(
                                    "${arrayVariable.name}$$i",
                                    SimpleTypeDeclaration(
                                            baseType = baseType,
                                            initialization = init))
                            if (arrayVariable.isGlobal) {
                                `var`.type = VariableDeclaration.GLOBAL
                                state.theProgram!!.scope.add(`var`)
                            }
                        }
                        val arrayEmbedderVisitor = ArrayEmbedderVisitor(arrayVariable)
                        state.functions.values.forEach { f -> f.accept(arrayEmbedderVisitor) }
                        state.theProgram!!.accept(arrayEmbedderVisitor)
                        state.functions.values.forEach { f -> f.accept(arrayEmbedderVisitor) }
                        state.theProgram!!.accept(arrayEmbedderVisitor)
                        state.theProgram!!.scope.asMap().remove(arrayVariable.name)
                    }
                    //System.out.println("Counted " + instanceCount + " instances");
                }
    }

    private class ArrayAccessRenameVisitor : AstMutableVisitor() {
        /**
         * Name of the array which isType accessed.
         */
        val toRename: String? = null
        /**
         * Index to be accessed.
         */
        val access: Int = 0
        /**
         * Subscript, i.e., the value of the index being accessed.
         */
        val subscript: Expression? = null

        override fun visit(symbolicReference: SymbolicReference): Expression {
            if (symbolicReference.identifier == toRename && symbolicReference.hasSubscripts()) {
                symbolicReference.identifier = "$toRename$$access"
                symbolicReference.subscripts = null
            } else if (subscript is SymbolicReference && symbolicReference == subscript)
                return Literal.integer(access)// Set constant value for subscript (if it isType a symbolic reference)
            return super.visit(symbolicReference)
        }
    }

    private inner class ArrayEmbedderVisitor(val arrayVariable: VariableDeclaration) : AstMutableVisitor() {

        override fun visit(statements: StatementList): StatementList {
            return statements
            // First branch the entire code block for read-only variables
            /*val newStatements = findAndBranch(statements, FindReferenceWithSubscriptVisitor(
                    { symbolicReference ->
                        if (symbolicReference.getIdentifiedObject() !isType VariableDeclaration)
                            return@findAndBranch false
                        val `var` = symbolicReference.getIdentifiedObject() as VariableDeclaration
                        `var`.isInput
                    }))
            //TODO
            val newStatements: Top = StatementList()
            assert(newStatements isType Statement || newStatements isType StatementList)
            statements = if (newStatements isType Statement)
                StatementList(newStatements)
            else
                newStatements as StatementList
            // Now the rest
            val statementList = StatementList()
            for (statement in statements) {
                // We need to handle guarded statements differently since the guard cannot contain another if statement
                if (statement isType IfStatement) {
                    val (conditionalBranches, elseBranch) = statement
                    val newIfStatement = IfStatement()
                    for ((condition, statements1) in conditionalBranches)
                        newIfStatement.addGuardedCommand(condition,
                                statements1.accept<Any>(this) as StatementList)
                    newIfStatement.elseBranch = elseBranch.accept<Any>(this) as StatementList
                    statement = newIfStatement
                } else if (statement isType CaseStatement) {
                    val (expression, cases, elseCase) = statement
                    val newCaseStatement = CaseStatement()
                    newCaseStatement.expression = expression
                    for (c in cases)
                        newCaseStatement.addCase(CaseStatement.Case(
                                c.getConditions(), c.getStatements().accept(this) as StatementList
                        ))
                    newCaseStatement.elseCase = elseCase!!.accept<Any>(this) as StatementList
                    statement = newCaseStatement
                } else if (statement isType GuardedStatement) {
                    statement.statements = statement.statements.accept<Any>(this) as StatementList
                    //statement = guardedStatement;
                }
                statementList.add(findAndBranch(statement, FindReferenceWithSubscriptVisitor()) as Statement)
            }
            return statementList
        */
        }

        /*private fun findAndBranch(codeBlock: Visitable, subscriptFinder: FindReferenceWithSubscriptVisitor): Any {
            assert(codeBlock isType Statement || codeBlock isType StatementList)
            codeBlock.accept<Any>(subscriptFinder)
            val branch = IfStatement()
            while (subscriptFinder.found()) {
                val instanceReference = subscriptFinder.theReference
                // TODO multiple subscripts
                val subscript = instanceReference!!.subscripts!![0]
                // Add branches based on the instance reference we found
                val array = state!!.theProgram!!.scope.getVariable(instanceReference).typeDeclaration as ArrayTypeDeclaration?
                // TODO multiple ranges
                val range = array!!.ranges[0]
                val rangeType = RangeType(range.startValue, range.stopValue, DataTypes.getUSINT())
                val values = HashSet<Int>()
                if (subscript isType SymbolicReference) {
                    var r: SymbolicReference? = subscript
                    while (r!!.hasSub())
                        r = r.sub
                    if (r.getIdentifiedObject() isType VariableDeclaration) {
                        val variable = r.getIdentifiedObject() as VariableDeclaration
                        if (!state!!.stooState.getInstancesOfVariable(variable).isEmpty())
                            state!!.stooState.getInstancesOfVariable(variable).parallelStream()
                                    .map({ i -> state!!.stooState.getInstanceID(i) })
                                    .forEach(???({ values.add() }))
                        else
                        try {
                            state!!.stooState.getEffectiveSubtypeScope()
                                    .getTypes(variable).parallelStream()
                                    .map({ t ->
                                        state!!.stooState.getInstanceIDRangesToClass(
                                                (t as ClassDataType).clazz)
                                    })
                                    .forEach { pairs ->
                                        pairs.parallelStream()
                                                .forEach { p ->
                                                    IntStream.range(p.getA(), p.getB() + 1)
                                                            .forEach(IntConsumer { values.add(it) })
                                                }
                                    }
                        } catch (ignored: NoSuchElementException) {
                        }

                    }
                }
                if (values.isEmpty()) {
                    val rangeMin = Integer.parseInt(range.start.text)
                    for (i in rangeMin..Integer.parseInt(range.stop.text))
                        values.add(i)
                }
                instanceCount += values.size.toLong()
                for (i in values) {
                    val block = if (codeBlock isType Statement)
                        StatementList(codeBlock.clone())
                    else
                        StatementList((codeBlock as StatementList).clone())
                    block.accept<Any>(ArrayAccessRenameVisitor(instanceReference.identifier, i, subscript))
                    branch.addGuardedCommand(GuardedStatement(
                            BinaryExpression.Companion.equalsExpression(subscript, Literal(rangeType, Integer.toString(i))),
                            block))
                }
                // Perform search once more
                subscriptFinder.reset()
            }
            return if (branch.conditionalBranches.isEmpty())
            // Keep statements intact we case we don't find anything to rename
                codeBlock
            else if (branch.conditionalBranches.size == 1)
            // Only one condition branch, no need for IF
                branch.conditionalBranches[0].statements[0]
            else
                branch
        }*/

        /*
        @Getter
        @RequiredArgsConstructor
        private inner class FindReferenceWithSubscriptVisitor : AstVisitor<Any> {
            val match: Function<SymbolicReference, Boolean>
            var theReference: SymbolicReference? = null
                private set

            internal constructor() {
                match = { symbolicReference -> true }
            }

            internal fun found(): Boolean {
                return theReference != null
            }

            fun defaultVisit(visitable: Visitable): Any? {
                return if (found()) null else super.defaultVisit(visitable)
            }

            override fun visit(symbolicReference: SymbolicReference): Any? {
                if (found())
                    return null
                // TODO multiple subscripts
                if (symbolicReference.identifier == arrayVariable!!.name
                        && symbolicReference.hasSubscripts()
                        && symbolicReference.subscripts!![0] isType SymbolicReference
                        && match.apply(symbolicReference.subscripts!![0] as SymbolicReference))
                    theReference = symbolicReference
                if (symbolicReference.hasSub())
                    symbolicReference.sub!!.accept<Any>(this)
                if (symbolicReference.hasSubscripts())
                    symbolicReference.subscripts!!.accept<Any>(this)
                return super.visit(symbolicReference)
            }

            internal fun reset() {
                theReference = null
            }
        }*/
    }
}
