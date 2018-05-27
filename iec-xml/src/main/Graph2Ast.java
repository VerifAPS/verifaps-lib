package edu.kit.iti.formal.automation.plcopenxml;

/*-
 * #%L
 * jpox
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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.st.ast.*;

/**
 * @author weigla
 * @date 24.06.2014
 */
public class Graph2Ast {
    public static final String STATE_VARIABLE = "_state";
    private static final String TRANSIT_VARIABLE = "_transit";

    SFCGraph graph;
    EnumerationTypeDeclaration enumStates;

    public Graph2Ast(SFCGraph graph) {
        this.graph = graph;
    }


    private String getStatesTypeName() {
        return graph.getName() + "_states_t";
    }

    public FunctionBlockDeclaration getFunctionBlock() {
        FunctionBlockDeclaration fbd = new FunctionBlockDeclaration();
        VariableBuilder vb = graph.getScope().builder();

        vb.clear(VariableDeclaration.LOCAL);
        vb.setBaseType(getStatesTypeName()).identifiers(STATE_VARIABLE).close();
        vb.setBaseType("BOOL").identifiers(TRANSIT_VARIABLE).close();

        fbd.setFunctionBlockName(graph.getName());
        fbd.setScope(graph.getScope());

        enumStates = new EnumerationTypeDeclaration();
        enumStates.setTypeName(getStatesTypeName());

        //gather all states into the enum declaration
        for (SFCGraph.Node n : graph.getNodes()) {
            if (n instanceof SFCGraph.Step) {
                enumStates.addValue(n.name);
                if (((SFCGraph.Step) n).initial) {
                    enumStates.setInitialization(new ScalarValue<>(null, n.name));
                }
            }
        }

        CaseStatement theBigCase = new CaseStatement();
        theBigCase.setExpression(new SymbolicReference(STATE_VARIABLE));

        for (SFCGraph.Node n : graph.getNodes()) {
            if (n instanceof SFCGraph.Step)
                theBigCase.addCase(caseFor((SFCGraph.Step) n));
        }

        fbd.getFunctionBody().add(theBigCase);
        return fbd;
    }


    private CaseStatement.Case caseFor(SFCGraph.Step n) {
        CaseStatement.Case esac = new CaseStatement.Case();

        esac.addCondition(new CaseConditions.Enumeration(getStatesTypeName() + "#" + n.name));
        StatementList sl = esac.getStatements();

        sl.comment("begin(State)");


        sl.comment("begin(onEntry)");
        if (n.onEntry != null) {
            IfStatement ifEntry = new IfStatement();
            GuardedStatement gc = new GuardedStatement(new SymbolicReference(TRANSIT_VARIABLE), n.onEntry);
            ifEntry.addGuardedCommand(gc);
            sl.add(ifEntry);
        }
        sl.add(assignment(TRANSIT_VARIABLE, "FALSE"));
        sl.comment("end(onEntry)");

        //build in active
        sl.comment("begin(onActive)");
        if (n.onWhile != null)
            sl.addAll(n.onWhile);
        sl.comment("end(onActive)");

        sl.comment("begin(transition)");
        IfStatement transitions = new IfStatement();
        Statement assignExitTrue = assignment(TRANSIT_VARIABLE, "TRUE");

        for (SFCGraph.Transition t : n.outgoing) {
            StatementList assignNextState = IEC61131Facade.statements(String.format("%s := %s#%s;",
                    STATE_VARIABLE, getStatesTypeName(), t.to.name));
            GuardedStatement gc = new GuardedStatement();
            gc.setCondition(IECExpressions.combine(Operators.AND, t.conditions));
            gc.getStatements().add(assignExitTrue);
            gc.getStatements().addAll(assignNextState);
            transitions.getConditionalBranches().add(gc);
        }
        sl.add(transitions);
        sl.comment(("end(transition)"));

        sl.comment("begin(onExit)");
        if (n.onExit != null) {
            IfStatement ifExit = new IfStatement();
            ifExit.addGuardedCommand(new SymbolicReference(TRANSIT_VARIABLE), n.onExit);
            sl.add(ifExit);
        }
        sl.comment("end(onExit)");
        sl.comment("end(State)");
        return esac;
    }

    private IfStatement ifstatement(String condigtion, Statement then) {
        IfStatement _if = new IfStatement();
        _if.addGuardedCommand(IEC61131Facade.expr(condigtion), new StatementList(then));
        return _if;
    }

    private Statement assignment(String var, String expression) {
        AssignmentStatement a = new AssignmentStatement(new SymbolicReference(var, null),
                IEC61131Facade.expr(expression));
        return a;
    }
}
