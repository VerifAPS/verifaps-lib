package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.st.ast.*

import java.util.HashSet
import java.util.stream.Collectors

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class WriteBeforeReadIdentifier : AstVisitor<WriteBeforeReadIdentifier.WBRState>() {

    private var current: WBRState? = null

    class WBRState {
        internal var readed: MutableSet<String> = HashSet()
        internal var candidates: MutableSet<String> = HashSet()
        internal var violates: MutableSet<String> = HashSet()


        fun write(name: String?) {
            if (!readed.contains(name))
                candidates.add(name)
            else
                violates.add(name)
        }

        fun read(name: String) {
            readed.add(name)
        }

        fun add(w: WBRState) {
            if (candidates.size == 0) {
                candidates = w.candidates
            } else {
                candidates.retainAll(w.candidates)
            }


            readed.addAll(w.readed)
            violates.addAll(w.violates)
        }

        fun seq(w: WBRState) {
            for (wr in w.candidates)
                write(wr)
            readed.addAll(w.readed)
            violates.addAll(w.violates)
        }
    }

    /** {@inheritDoc}  */
    override fun visit(assignmentStatement: AssignmentStatement): WBRState? {
        val wbrState = WBRState()
        current = wbrState
        assignmentStatement.expression.accept<WBRState>(this)
        val variable = assignmentStatement.location
        wbrState.write(variable.toString())
        return wbrState
    }

    /*@Override
    public WBRState accept(SymbolicReference symbolicReference) {
        current.read(symbolicReference.getName());
        return null;
    }*/

    /** {@inheritDoc}  */
    override fun visit(statements: StatementList): WBRState? {
        val state = WBRState()
        for (s in statements) {
            val w = s.accept<WBRState>(this)
            state.seq(w)
        }
        return state
    }

    /** {@inheritDoc}  */
    override fun visit(fbc: InvocationStatement): WBRState? {
        val state = WBRState()

        for (`in` in fbc.parameters)
            if (!`in`.isOutput) {
                val s = `in`.expression!!.accept<WBRState>(this)
                state.add(s)
            }

        for (`in` in fbc.parameters)
            if (`in`.isOutput)
                state.write(`in`.name)

        return state
    }

    /** {@inheritDoc}  */
    override fun visit(commentStatement: CommentStatement): WBRState? {
        return WBRState()
    }

    /** {@inheritDoc}  */
    override fun visit(ifStatement: IfStatement): WBRState? {
        val cond = ifStatement.conditionalBranches.stream().map<WBRState>(Function<GuardedStatement, WBRState> { this.visit(it) }).collect<List<WBRState>, Any>(Collectors.toList())

        val state = WBRState()

        for (wbrState in cond) {

            state.add(wbrState)
        }

        if (ifStatement.elseBranch.size > 0) {
            val elseState = ifStatement.elseBranch.accept(this)
            state.add(elseState)
        }

        state.candidates.removeAll(state.violates)

        return state
    }

    /** {@inheritDoc}  */
    override fun visit(guardedStatement: GuardedStatement): WBRState? {
        val state = WBRState()
        current = state

        guardedStatement.condition.accept<WBRState>(this)
        current = guardedStatement.statements.accept(this)

        for (candidate in current!!.candidates) {
            state.write(candidate)
        }

        state.readed.addAll(current!!.readed)
        state.violates.addAll(current!!.violates)

        return state
    }

    /** {@inheritDoc}  */
    override fun visit(aCase: CaseStatement.Case): WBRState? {
        return aCase.statements.accept(this)
    }

    /** {@inheritDoc}  */
    override fun visit(caseStatement: CaseStatement): WBRState? {
        val state = WBRState()
        current = state
        caseStatement.expression!!.accept<WBRState>(this)


        val cond = caseStatement.cases.stream().map<WBRState>(Function<Case, WBRState> { this.visit(it) }).collect<List<WBRState>, Any>(Collectors.toList())

        val cases = WBRState()
        for (wbrState in cond) {
            cases.add(wbrState)
        }


        if (caseStatement.elseCase!!.size > 0) {
            val elseState = caseStatement.elseCase!!.accept(this)
            cases.add(elseState)

        }

        state.seq(cases)
        state.candidates.removeAll(state.violates)

        return state
    }

    /** {@inheritDoc}  */
    override fun visit(programDeclaration: ProgramDeclaration): WBRState? {
        return programDeclaration.stBody!!.accept(this)
    }

    companion object {

        /**
         *
         * investigate.
         *
         * @param visitable a [edu.kit.iti.formal.automation.visitors.Visitable] object.
         * @return a [java.util.Set] object.
         */
        fun investigate(visitable: Visitable): Set<String> {
            val wbri = WriteBeforeReadIdentifier()
            return visitable.accept(wbri).candidates
        }
    }
}
