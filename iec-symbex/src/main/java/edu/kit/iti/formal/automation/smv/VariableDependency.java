package edu.kit.iti.formal.automation.smv;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.SMVAstDefaultVisitor;
import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class VariableDependency {
    private final SymbolicState state;

    public VariableDependency(SymbolicState finalState) {
        state = finalState;
    }

    public Set<SVariable> dependsOn(Collection<VariableDeclaration> names,
                                    List<VariableDeclaration> ignoredVars) {
        Set<SVariable> reached = names.stream()
                .map(SymbExFacade::asSVariable)
                .collect(Collectors.toSet());

        Set<SVariable> ignored = ignoredVars.stream()
                .map(SymbExFacade::asSVariable)
                .collect(Collectors.toSet());

        VarVisitor vv = new VarVisitor(reached, ignored);

        //fixpoint
        boolean changed = false;
        do {
            LinkedList<SVariable> backup = new LinkedList<>(reached);
            for (SVariable name : backup) {
                SMVExpr e = state.get(name);
                if (e != null) e.accept(vv);
            }
            changed = backup.size() != reached.size();
        } while (changed);

        return reached;
    }

    static class VarVisitor extends SMVAstDefaultVisitor<Void> {
        private final Set<SVariable> ignored;
        private final Set<SVariable> reached;

        public VarVisitor(Set<SVariable> reached, Set<SVariable> deps) {
            this.reached = reached;
            this.ignored = deps;
        }

        @Override
        public Void visit(SMVAst top) {
            return null;
        }

        @Override
        public Void visit(SVariable v) {
            if (!ignored.contains(v))
                reached.add(v);
            return null;
        }

        @Override
        public Void visit(SBinaryExpression be) {
            be.left.accept(this);
            be.right.accept(this);
            return null;
        }

        @Override
        public Void visit(SUnaryExpression ue) {
            ue.expr.accept(this);
            return null;
        }

        @Override
        public Void visit(SLiteral l) {
            return null;
        }

        @Override
        public Void visit(SAssignment a) {
            return null;
        }

        @Override
        public Void visit(SCaseExpression ce) {
            for (SCaseExpression.Case c : ce.cases) {
                c.condition.accept(this);
                c.then.accept(this);
            }
            return null;
        }

        @Override
        public Void visit(SMVModule smvModule) {
            return null;
        }

        @Override
        public Void visit(SFunction func) {
            func.getArguments().forEach(a -> a.accept(this));
            return null;
        }
    }
}
