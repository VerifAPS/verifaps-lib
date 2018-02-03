package edu.kit.iti.formal.automation.st.util;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class WriteBeforeReadIdentifier extends AstVisitor<WriteBeforeReadIdentifier.WBRState> {
    public static class WBRState {
        Set<String> readed = new HashSet<>();
        Set<String> candidates = new HashSet<>();
        Set<String> violates = new HashSet<>();


        public void write(String name) {
            if (!readed.contains(name))
                candidates.add(name);
            else
                violates.add(name);
        }

        public void read(String name) {
            readed.add(name);
        }

        public void add(WBRState w) {
            if (candidates.size() == 0) {
                candidates = w.candidates;
            } else {
                candidates.retainAll(w.candidates);
            }


            readed.addAll(w.readed);
            violates.addAll(w.violates);
        }

        public void seq(WBRState w) {
            for (String wr : w.candidates)
                write(wr);
            readed.addAll(w.readed);
            violates.addAll(w.violates);
        }
    }

    private WBRState current;

    /** {@inheritDoc} */
    @Override
    public WBRState visit(AssignmentStatement assignmentStatement) {
        WBRState wbrState = new WBRState();
        current = wbrState;
        assignmentStatement.getExpression().accept(this);
        Reference variable = assignmentStatement.getLocation();
        wbrState.write(variable.toString());
        return wbrState;
    }

    /*@Override
    public WBRState accept(SymbolicReference symbolicReference) {
        current.read(symbolicReference.getIdentifier());
        return null;
    }*/

    /** {@inheritDoc} */
    @Override
    public WBRState visit(StatementList statements) {
        WBRState state = new WBRState();
        for (Statement s : statements) {
            WBRState w = s.accept(this);
            state.seq(w);
        }
        return state;
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(InvocationStatement fbc) {
        WBRState state = new WBRState();

        for (Invocation.Parameter in : fbc.getParameters())
            if (!in.isOutput()) {
                WBRState s = in.getExpression().accept(this);
                state.add(s);
            }

        for (Invocation.Parameter in : fbc.getParameters())
            if (in.isOutput())
                state.write(in.getName());

        return state;
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(CommentStatement commentStatement) {
        return new WBRState();
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(IfStatement ifStatement) {
        List<WBRState> cond = ifStatement.getConditionalBranches().stream().map(this::visit).collect(Collectors.toList());

        WBRState state = new WBRState();

        for (WBRState wbrState : cond) {

            state.add(wbrState);
        }

        if (ifStatement.getElseBranch().size() > 0) {
            WBRState elseState = ifStatement.getElseBranch().accept(this);
            state.add(elseState);
        }

        state.candidates.removeAll(state.violates);

        return state;
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(GuardedStatement guardedStatement) {
        WBRState state = new WBRState();
        current = state;

        guardedStatement.getCondition().accept(this);
        current = guardedStatement.getStatements().accept(this);

        for (String candidate : current.candidates) {
            state.write(candidate);
        }

        state.readed.addAll(current.readed);
        state.violates.addAll(current.violates);

        return state;
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(CaseStatement.Case aCase) {
        return aCase.getStatements().accept(this);
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(CaseStatement caseStatement) {
        WBRState state = new WBRState();
        current = state;
        caseStatement.getExpression().accept(this);


        List<WBRState> cond = caseStatement.getCases().stream().map(this::visit).collect(Collectors.toList());

        WBRState cases = new WBRState();
        for (WBRState wbrState : cond) {
            cases.add(wbrState);
        }


        if (caseStatement.getElseCase().size() > 0) {
            WBRState elseState = caseStatement.getElseCase().accept(this);
            cases.add(elseState);

        }

        state.seq(cases);
        state.candidates.removeAll(state.violates);

        return state;
    }

    /** {@inheritDoc} */
    @Override
    public WBRState visit(ProgramDeclaration programDeclaration) {
        return programDeclaration.getStBody().accept(this);
    }

    /**
     * <p>investigate.</p>
     *
     * @param visitable a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @return a {@link java.util.Set} object.
     */
    public static Set<String> investigate(Visitable visitable) {
        WriteBeforeReadIdentifier wbri = new
                WriteBeforeReadIdentifier();
        return visitable.accept(wbri).candidates;
    }
}
