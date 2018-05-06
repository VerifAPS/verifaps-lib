package edu.kit.iti.formal.smv.printers;

import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

import java.util.List;
import java.util.Map;
import java.util.TreeSet;

/**
 * @author Augusto Modanese
 */
public abstract class Printer implements SMVAstVisitor<Object> {
    @Override
    public Object visit(SMVAst top) {
        throw new IllegalArgumentException("not implemented for " + top);
    }

    @Override
    public Object visit(SBinaryExpression be) {
        int pleft = precedence(be.left);
        int pright = precedence(be.right);
        int pown = precedence(be);

        if (pleft > pown) {
            print("(");
            be.left.accept(this);
            print(")");
        }
        else
            be.left.accept(this);

        print(" " + be.operator.symbol() + " ");

        if (pright > pown) {
            print("(");
            be.right.accept(this);
            print(")");
        }
        else
            be.right.accept(this);

        return null;
    }

    private int precedence(SMVExpr expr) {
        if (expr instanceof SBinaryExpression) {
            SBinaryExpression binaryExpression = (SBinaryExpression) expr;
            return binaryExpression.operator.precedence();
        }
        if (expr instanceof SUnaryExpression) {
            SUnaryExpression sUnaryExpression = (SUnaryExpression) expr;
            return sUnaryExpression.operator.precedence();
        }

        if (expr instanceof SLiteral || expr instanceof SVariable
                || expr instanceof SFunction) {
            return -1;
        }

        return 1000;
    }

    @Override
    public Object visit(SUnaryExpression ue) {
        print(ue.operator.symbol());
        if (ue.expr instanceof SBinaryExpression) {
            print("(");
            ue.expr.accept(this);
            print(")");
        }
        else
            ue.expr.accept(this);
        return null;
    }

    @Override
    public Object visit(SLiteral l) {
        print(l.getSMVType().format(l.value));
        return null;
    }

    @Override
    public Object visit(SAssignment a) {
        a.target.accept(this);
        print(" := ");
        a.expr.accept(this);
        print(";\n");
        return null;
    }

    @Override
    public Object visit(SCaseExpression ce) {
        print("case \n");
        for (SCaseExpression.Case esac : ce.cases) {
            esac.condition.accept(this);
            print(" : ");
            esac.then.accept(this);
            print("; ");
        }
        print("\nesac");
        return null;
    }

    @Override
    public Object visit(SMVModule m) {
        print("MODULE " + m.getName());
        if (!m.getModuleParameters().isEmpty()) {
            print("(");
            for (int i = 0; i < m.getModuleParameters().size(); i++) {
                m.getModuleParameters().get(i).accept(this);
                if (i < m.getModuleParameters().size() - 1)
                    print(", ");
            }
            print(")");
        }
        print("\n");

        printVariables("IVAR", m.getInputVars());
        printVariables("FROZENVAR", m.getFrozenVars());
        printVariables("VAR", m.getStateVars());

        printAssignments("DEFINE", m.getDefinitions());

        printSection("LTLSPEC", m.getLtlSpec());
        printSection("CTLSPEC", m.getCtlSpec());
        printSection("INVARSPEC", m.getInvariantSpecs());
        printSection("INVAR", m.getInvariants());
        printSectionSingle("INIT", m.getInitExpr());
        printSectionSingle("TRANS", m.getTransExpr());


        if (m.getInit().size() > 0 || m.getNext().size() > 0) {
            print("ASSIGN\n");
            printAssignments(m.getInit(), "init");
            printAssignments(m.getNext(), "next");
        }

        print("\n-- end of module " + m.getName() + '\n');
        return null;
    }

    private void printSectionSingle(String section, List<SMVExpr> exprs) {
        if (!exprs.isEmpty()) {
            print(section + "\n" + "\t");
            SMVFacade.combine(SBinaryOperator.AND, exprs).accept(this);
            print(";\n");
        }
    }

    private void printAssignments(List<SAssignment> assignments, String func) {
        for (SAssignment a : assignments) {
            print("\t" + func + '(' + a.target.getName() + ") := ");
            a.expr.accept(this);
            print(";\n");
        }
    }

    private void printSection(String section, List<SMVExpr> exprs) {
        if (exprs.size() > 0) {
            for (SMVExpr e : exprs) {
                if (e == null) continue;
                print(section + "\n\t");
                e.accept(this);
                print(";\n\n");
            }
        }
    }

    private void printAssignments(String section, Map<SVariable, SMVExpr> definitions) {
        if (definitions.size() > 0) {
            TreeSet<SVariable> keys = new TreeSet<>(definitions.keySet());

            print(section + "\n");
            for (SVariable k : keys) {
                print("\t" + k.getName() + " := ");
                definitions.get(k).accept(this);
                print(";\n");
            }
        }
    }

    @Override
    public Object visit(SFunction func) {
        print(func.getName() + "(");
        for (int i = 0; i < func.getArguments().size(); i++) {
            func.getArguments().get(i).accept(this);
            if (i < func.getArguments().size() - 1)
                print(", ");
        }
        print(")");
        return null;
    }

    @Override
    public Object visit(SQuantified quantified) {
        switch (quantified.getOperator().arity()) {
            case 1:
                print(quantified.getOperator().symbol() + "(");
                quantified.getQuantified(0).accept(this);
                print(")");
                return null;
            case 2:
                print("(");
                quantified.getQuantified(0).accept(this);
                print(")" + quantified.getOperator().symbol() + "(");
                quantified.getQuantified(1).accept(this);
                print(")");
                return null;
            default:
                throw new IllegalStateException("too much arity");
        }
    }

    private void printVariables(String type, List<SVariable> vars) {
        if (vars.size() != 0) {
            print(type + "\n");
            for (SVariable var : vars)
                print("\t" + var.getName() + " : "  + var.getSMVType() + ";\n");
            print("-- end of " + type + "\n");
        }
    }


    @Override
    public Object visit(SVariable v) {
        print(v.getName());
        return null;
    }

    /**
     * Process the given string.
     * @param s the string to process
     */
    abstract void print(String s);
}
