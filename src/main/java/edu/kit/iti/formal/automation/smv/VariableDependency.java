package edu.kit.iti.formal.automation.smv;

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class VariableDependency {
    private final SymbolicState state;

    public VariableDependency(SymbolicState finalState) {
        state = finalState;
    }

    public Set<String> dependsOn(Collection<VariableDeclaration> names) {
        Set<String> d = new HashSet<>();
        VarVisitor vv = new VarVisitor(d);

        for (VariableDeclaration name : names) {
            state.get(SymbExFacade.asSVariable(name)).accept(vv);
        }

        return d;
    }

    static class VarVisitor implements SMVAstVisitor<Void> {
        private Set<String> deps;

        public VarVisitor(Set<String> deps) {
            this.deps = deps;
        }

        @Override
        public Void visit(SMVAst top) {
            return null;
        }

        @Override
        public Void visit(SVariable v) {
            deps.add(v.name);
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
            Arrays.stream(func.getArguments()).forEach(a -> a.accept(this));
            return null;
        }
    }
}
