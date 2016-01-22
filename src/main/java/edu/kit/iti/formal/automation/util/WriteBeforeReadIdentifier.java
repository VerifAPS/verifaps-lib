package edu.kit.iti.formal.automation.util;

import edu.kit.iti.formal.automation.ast.*;
import edu.kit.iti.formal.automation.visitors.Visitable;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by weigl on 10/07/14.
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

    @Override
    public WBRState visit(AssignmentStatement assignmentStatement) {
        WBRState wbrState = new WBRState();
        current = wbrState;
        assignmentStatement.getExpression().visit(this);
        SymbolicReference variable = (SymbolicReference) assignmentStatement.getVariable();
        wbrState.write(variable.getIdentifier());
        return wbrState;
    }

    @Override
    public WBRState visit(SymbolicReference symbolicReference) {
        current.read(symbolicReference.getIdentifier());
        return null;
    }

    @Override
    public WBRState visit(StatementList statements) {
        WBRState state = new WBRState();
        for (Statement s : statements) {
            WBRState w = s.visit(this);
            state.seq(w);
        }
        return state;
    }

    @Override
    public WBRState visit(FunctionCallStatement functionCallStatement) {
        WBRState state = new WBRState();

        for (FunctionCall.Parameter in : functionCallStatement.getFunctionCall().getParameters())
            if (!in.isOutput()) {
                WBRState s = in.getExpression().visit(this);
                state.add(s);
            }

        for (FunctionCall.Parameter in : functionCallStatement.getFunctionCall().getParameters())
            if (in.isOutput())
                state.write(in.getName());

        return state;
    }

    @Override
    public WBRState visit(CommentStatement commentStatement) {
        return new WBRState();
    }

    @Override
    public WBRState visit(IfStatement ifStatement) {
        List<WBRState> cond = ifStatement.getConditionalBranches().stream().map(this::visit).collect(Collectors.toList());

        WBRState state = new WBRState();

        for (WBRState wbrState : cond) {

            state.add(wbrState);
        }

        if (ifStatement.getElseBranch().size() > 0) {
            WBRState elseState = ifStatement.getElseBranch().visit(this);
            state.add(elseState);
        }

        state.candidates.removeAll(state.violates);

        return state;
    }

    @Override
    public WBRState visit(GuardedStatement guardedStatement) {
        WBRState state = new WBRState();
        current = state;

        guardedStatement.getCondition().visit(this);
        current = guardedStatement.getStatements().visit(this);

        for (String candidate : current.candidates) {
            state.write(candidate);
        }

        state.readed.addAll(current.readed);
        state.violates.addAll(current.violates);

        return state;
    }

    @Override
    public WBRState visit(CaseStatement.Case aCase) {
        return aCase.getStatements().visit(this);
    }

    @Override
    public WBRState visit(CaseStatement caseStatement) {
        WBRState state = new WBRState();
        current = state;
        caseStatement.getExpression().visit(this);


        List<WBRState> cond = caseStatement.getCases().stream().map(this::visit).collect(Collectors.toList());

        WBRState cases = new WBRState();
        for (WBRState wbrState : cond) {
            cases.add(wbrState);
        }


        if (caseStatement.getElseCase().size() > 0) {
            WBRState elseState = caseStatement.getElseCase().visit(this);
            cases.add(elseState);

        }

        state.seq(cases);
        state.candidates.removeAll(state.violates);

        return state;
    }

    @Override
    public WBRState visit(ProgramDeclaration programDeclaration) {
        return programDeclaration.getProgramBody().visit(this);
    }

    public static Set<String> investigate(Visitable visitable) {
        WriteBeforeReadIdentifier wbri = new
                WriteBeforeReadIdentifier();
        return visitable.visit(wbri).candidates;
    }
}
