package edu.kit.iti.formal.smv;

/*-
 * #%L
 * smv-model
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

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SCaseExpression.Case;
import edu.kit.iti.formal.smv.ast.SVariable;

public class Printer implements SMVAstVisitor<String> {

    @Override
    public String visit(SMVAst top) {
        throw new IllegalArgumentException("not implemented for " + top);
    }

    @Override
    public String visit(SBinaryExpression be) {
        int pleft = precedence(be.left);
        int pright = precedence(be.right);
        int pown = precedence(be);

        String a = be.left.accept(this);
        String b = be.right.accept(this);

        return (pleft > pown ? "(" + a + ")" : a)
                + " " + be.operator.symbol() + " "
                + (pright > pown ? "(" + b + ")" : b);
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
    public String visit(SUnaryExpression ue) {
        if (ue.expr instanceof SBinaryExpression) {
            return ue.operator.symbol() + "(" + ue.expr.accept(this) + ")";
        }
        return ue.operator.symbol() + ue.expr.accept(this);
    }

    @Override
    public String visit(SLiteral l) {
        return l.getSMVType().format(l.value);
    }

    @Override
    public String visit(SAssignment a) {
        return a.target.accept(this) + " := " + a.expr.accept(this) + ";\n";
    }

    @Override
    public String visit(SCaseExpression ce) {
        StringBuilder sb = new StringBuilder();
        sb.append("case \n");
        for (Case esac : ce.cases) {
            sb.append(esac.condition.accept(this)).append(" : ")
                    .append(esac.then.accept(this))
                    .append("; ");
        }

        sb.append("\nesac");
        return sb.toString();
    }


    public static String toString(SMVModule m) {
        Printer p = new Printer();
        return p.visit(m);
    }

    @Override
    public String visit(SMVModule m) {
        StringBuilder sb = new StringBuilder();
        sb.append("MODULE ").append(m.getName());
        if (!m.getModuleParameter().isEmpty()) {
            sb.append("(").append(
                    m.getModuleParameter().stream()
                            .map(p -> p.getName())
                            .reduce((a, b) -> a + ", " + b)
                            .get())
                    .append(")");
        }
        sb.append('\n');

        printVariables(sb, "IVAR", m.getInputVars());
        printVariables(sb, "FROZENVAR", m.getFrozenVars());
        printVariables(sb, "VAR", m.getStateVars());

        printAssignments(sb, "DEFINE", m.getDefinitions());

        printSection(sb, "LTLSPEC", m.getLTLSpec());
        printSection(sb, "CTLSPEC", m.getCTLSpec());
        printSection(sb, "INVARSPEC", m.getInvarSpec());
        printSection(sb, "INVAR", m.getInvar());
        printSectionSingle(sb, "INIT", m.getInit());
        printSectionSingle(sb, "TRANS", m.getTrans());


        sb.append("ASSIGN\n");
        printAssignments(sb, m.getInitAssignments(), "init");
        printAssignments(sb, m.getNextAssignments(), "next");

        sb.append("\n-- end of module ").append(m.getName()).append('\n');
        return sb.toString();
    }

    private void printSectionSingle(StringBuilder sb, String section, List<SMVExpr> exprs) {
        if (!exprs.isEmpty()) {
            sb.append(section).append("\n");
            sb.append("\t")
                    .append(
                            SMVFacade.combine(SBinaryOperator.AND, exprs).accept(this)
                    ).append(";\n");
        }
    }

    private void printAssignments(StringBuilder sb, List<SAssignment> assignments, String func) {
        for (SAssignment a : assignments) {
            sb.append("\t")
                    .append(func)
                    .append('(')
                    .append(a.target.getName())
                    .append(") := ")
                    .append(a.expr.accept(this)).append(";\n");
        }
    }

    private void printSection(StringBuilder sb, String section, List<SMVExpr> exprs) {
        if (exprs.size() > 0) {
            for (SMVExpr e : exprs) {
                sb.append(section).append("\n\t");
                sb.append(e.accept(this)).append(";\n\n");
            }
        }
    }

    private void printAssignments(StringBuilder sb, String section,
                                  Map<SVariable, SMVExpr> definitions) {
        if (definitions.size() > 0) {
            TreeSet<SVariable> keys = new TreeSet<>(definitions.keySet());

            sb.append(section).append("\n");
            for (SVariable k : keys) {
                sb.append("\t")
                        .append(k.getName())
                        .append(" := ")
                        .append(definitions.get(k).accept(this))
                        .append(";\n");
            }
        }
    }

    @Override
    public String visit(SFunction func) {
        return func.getFunctionName() + "(" +
                Arrays.stream(func.getArguments())
                        .map(a -> a.accept(this))
                        .reduce((a, b) -> a + ", " + b)
                        .get()
                + ")";
    }

    private void printVariables(StringBuilder sb, String type, List<SVariable> vars) {
        if (vars.size() != 0) {
            sb.append(type).append('\n');

            for (SVariable var : vars) {
                sb.append('\t')
                        .append(var.getName())
                        .append(" : ")
                        .append(var.getSMVType())
                        .append(";\n");
            }

            sb.append("-- end of ").append(type).append('\n');
        }
    }

    @Override
    public String visit(SVariable v) {
        return v.getName();
    }
}
