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

import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SCaseExpression.Case;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

public class Printer implements SMVAstVisitor {
    private final PrintWriter sb;

    public Printer(String fileName, boolean append) throws FileNotFoundException {
        sb = new PrintWriter(new FileOutputStream(new File(fileName), append));
    }

    public Printer(String fileName) throws FileNotFoundException {
        this(fileName, false);
    }

    public static void write(SMVModule m, String fileName, boolean append) throws FileNotFoundException {
        Printer p = new Printer(fileName, append);
        m.accept(p);
        p.sb.close();
    }

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
            sb.append("(");
            be.left.accept(this);
            sb.append(")");
        }
        else
            be.left.accept(this);

        sb.append(" ").append(be.operator.symbol()).append(" ");

        if (pright > pown) {
            sb.append("(");
            be.right.accept(this);
            sb.append(")");
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
        if (ue.expr instanceof SBinaryExpression) {
            sb.append(ue.operator.symbol()).append("(");
            ue.expr.accept(this);
            sb.append(")");
        }
        else {
            sb.append(ue.operator.symbol());
            ue.expr.accept(this);
        }

        return null;
    }

    @Override
    public Object visit(SLiteral l) {
        sb.append(l.getSMVType().format(l.value));

        return null;
    }

    @Override
    public Object visit(SAssignment a) {
        a.target.accept(this);
        sb.append(" := ");
        a.expr.accept(this);
        sb.println();

        return null;
    }

    @Override
    public Object visit(SCaseExpression ce) {
        sb.append("case").println();
        for (Case esac : ce.cases) {
            esac.condition.accept(this);
            sb.append(" : ");
            esac.then.accept(this);
            sb.append("; ");
        }
        sb.println();
        sb.append("esac");

        return null;
    }

    @Override
    public Object visit(SMVModule m) {
        sb.append("MODULE ").append(m.getName());
        if (!m.getModuleParameter().isEmpty()) {
            sb.append("(");
            for (int i = 0; i < m.getModuleParameter().size(); i++) {
                m.getModuleParameter().get(i).accept(this);
                if (i < m.getModuleParameter().size() - 1)
                    sb.append(", ");
            }
            sb.append(")");
        }
        sb.println();

        printVariables("IVAR", m.getInputVars());
        printVariables("FROZENVAR", m.getFrozenVars());
        printVariables("VAR", m.getStateVars());

        printAssignments("DEFINE", m.getDefinitions());

        printSection("LTLSPEC", m.getLTLSpec());
        printSection("CTLSPEC", m.getCTLSpec());
        printSection("INVARSPEC", m.getInvarSpec());
        printSection("INVAR", m.getInvar());
        printSectionSingle("INIT", m.getInit());
        printSectionSingle("TRANS", m.getTrans());


        if (m.getInitAssignments().size() > 0 || m.getNextAssignments().size() > 0) {
            sb.println("ASSIGN");
            printAssignments(m.getInitAssignments(), "init");
            printAssignments(m.getNextAssignments(), "next");
        }

        sb.append("\n-- end of module ").append(m.getName()).append('\n');

        return null;
    }

    private void printSectionSingle(String section, List<SMVExpr> exprs) {
        if (!exprs.isEmpty()) {
            sb.append(section).println();
            sb.append("\t");
            SMVFacade.combine(SBinaryOperator.AND, exprs).accept(this);
            sb.append(";").println();
        }
    }

    private void printAssignments(List<SAssignment> assignments, String func) {
        for (SAssignment a : assignments) {
            sb.append("\t")
                    .append(func)
                    .append('(')
                    .append(a.target.getName())
                    .append(") := ");
            a.expr.accept(this);
            sb.append(";").println();
        }
    }

    private void printSection(String section, List<SMVExpr> exprs) {
        if (exprs.size() > 0) {
            for (SMVExpr e : exprs) {
                if(e==null) continue;
                sb.append(section).println();
                sb.append("\t");
                e.accept(this);
                sb.append(";").println();
                sb.println();
            }
        }
    }

    private void printAssignments(String section, Map<SVariable, SMVExpr> definitions) {
        if (definitions.size() > 0) {
            TreeSet<SVariable> keys = new TreeSet<>(definitions.keySet());

            sb.append(section).println();
            for (SVariable k : keys) {
                sb.append("\t")
                        .append(k.getName())
                        .append(" := ");
                definitions.get(k).accept(this);
                sb.append(";").println();
            }
        }
    }

    @Override
    public Object visit(SFunction func) {
        sb.append(func.getFunctionName()).append("(");
        for (int i = 0; i < func.getArguments().size(); i++) {
            func.getArguments().get(i).accept(this);
            if (i < func.getArguments().size() - 1)
                sb.append(", ");
        }
        sb.append(")");

        return null;
    }

    @Override
    public Object visit(SQuantified quantified) {
        switch (quantified.getOperator().arity()) {
            case 1:
                sb.append(quantified.getOperator().symbol()).append("(");
                quantified.getQuantified(0).accept(this);
                sb.append(")");
                break;
            case 2:
                sb.append("(");
                quantified.getQuantified(0).accept(this);
                sb.append(")")
                        .append(quantified.getOperator().symbol())
                        .append("(");
                quantified.getQuantified(1).accept(this);
                sb.append(")");
                break;
            default:
                throw new IllegalStateException("too much arity");
        }

        return null;
    }

    @Override
    public Object visit(SMVType.Module module) {
        sb.append(module.getModuleName()).append("(");
        for (int i = 0; i < module.getParameters().size(); i++) {
            module.getParameters().get(i).accept(this);
            if (i < module.getParameters().size() - 1)
                sb.append(", ");
        }
        sb.append(")");

        return null;
    }

    private void printVariables(String type, List<SVariable> vars) {
        if (vars.size() != 0) {
            sb.append(type).println();

            for (SVariable var : vars) {
                sb.append('\t')
                        .append(var.getName())
                        .append(" : ");
                if (var.getSMVType() instanceof SMVType.Module)
                    var.getSMVType().accept(this);
                else
                    sb.append(var.getSMVType().toString());
                sb.append(";").println();
            }

            sb.append("-- end of ").append(type).println();
        }
    }


    @Override
    public Object visit(SVariable v) {
        sb.append(v.getName());

        return null;
    }
}
