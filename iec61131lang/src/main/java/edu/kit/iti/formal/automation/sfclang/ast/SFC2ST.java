package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2018 Alexander Weigl
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

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.Setter;
import org.antlr.v4.runtime.CommonToken;

import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;

/**
 * @author Alexander Weigl
 * @version 1 (23.02.18)
 */
@RequiredArgsConstructor
public class SFC2ST implements Supplier<StatementList> {
    private final String name;
    @Getter
    private final SFCNetwork network;
    @Getter
    private final Scope scope;
    @Getter
    private final StatementList stBody = new StatementList();
    @Getter
    private EnumerationTypeDeclaration enumDecl = new EnumerationTypeDeclaration();
    @Getter
    @Setter
    private boolean sfcReset;
    private String stateVariable;
    private String transitVariable;

    @Override
    public StatementList get() {
        extractStates();
        addVariables();
        //actionAnalyses();
        addNonStoredVariablesReset(); // all non-stored assignments are reseted

        //code
        if (sfcReset) {
            embeddSFCReset();
        }

        createBigCase();
        return stBody;
    }

    private void actionAnalyses() {
        //System.out.println(name);
        Multimap<String, SFCActionQualifier.Qualifier> actionMap =
                HashMultimap.create();
        network.getSteps().stream().flatMap(s -> s.getEvents().stream())
                .filter(aa -> scope.hasVariable(aa.getActionName()))
                .forEach(aa -> actionMap.put(aa.getActionName(), aa.getQualifier().getQualifier()));
        System.out.println(actionMap);

        /*network.getSteps().stream().flatMap(s -> s.getOutgoing().stream())
                .filter(t -> t.getFrom().size()>1|| t.getTo().size()>1)
                //.forEach(t -> System.out.format("%d => %d%n", t.getFrom().size(), t.getTo().size()));
                .forEach(t -> System.out.format("%s => %s%n",
                        t.getFrom().stream().map(s->s.getName()).collect(Collectors.joining(",")),
                        t.getTo().stream().map(s->s.getName()).collect(Collectors.joining(","))));
        */
    }

    private void addNonStoredVariablesReset() {
        network.getSteps().stream().flatMap(s -> s.getEvents().stream())
                .filter(aa -> aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.NON_STORED)
                .filter(aa -> scope.hasVariable(aa.getActionName()))
                .forEach(aa -> {
                    stBody.add(new AssignmentStatement(
                            new SymbolicReference(aa.getActionName()),
                            Literal.FALSE
                    ));
                });
    }

    private void createBigCase() {
        CaseStatement statement = new CaseStatement();
        statement.setExpression(new SymbolicReference(stateVariable));
        stBody.add(statement);

        for (SFCStep step : network.getSteps()) {
            CaseStatement.Case _case = new CaseStatement.Case();
            CaseCondition cc = new CaseCondition.Enumeration(
                    new Literal(enumDecl.getTypeName(), step.getName()));
            _case.setConditions(Collections.singletonList(cc));
            statement.addCase(_case);
            StatementList sl = _case.getStatements();

            //transit
            IfStatement checkForTransit = new IfStatement();
            StatementList p1 = new StatementList();
            checkForTransit.addGuardedCommand(new SymbolicReference(transitVariable), p1);
            for (SFCStep.AssociatedAction aa : step.getEvents()) {
                if (aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.RAISING) {
                    p1.add(new InvocationStatement(aa.getActionName())); // actions allowed
                }
            }
            if (p1.size() > 0) {
                sl.add(checkForTransit);
            }
            sl.add(new AssignmentStatement(new SymbolicReference(transitVariable), Literal.FALSE));

            // S+N, R
            step.getEvents().stream().filter(aa ->
                    aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.SET ||
                            aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.NON_STORED)
                    .forEach(aa -> {
                        if (scope.hasVariable(aa.getActionName())) {
                            sl.add(new AssignmentStatement(new SymbolicReference(aa.getActionName()), Literal.TRUE));
                        } else {
                            sl.add(new InvocationStatement(aa.getActionName()));
                        }
                    });
            step.getEvents().stream().filter(aa ->
                    aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                    .forEach(aa -> {
                        if (scope.hasVariable(aa.getActionName())) {
                            sl.add(new AssignmentStatement(new SymbolicReference(aa.getActionName()), Literal.FALSE));
                        } else {
                            //Not handled!
                        }
                    });

            // outgoing transition
            step.getOutgoing().sort(new SFCTransition.PriorityComparison());
            step.getOutgoing().forEach(t -> {
                IfStatement _ifguard = new IfStatement();
                StatementList then = new StatementList();
                then.add(new AssignmentStatement(new SymbolicReference(transitVariable), Literal.TRUE));
                then.add(new AssignmentStatement(new SymbolicReference(stateVariable),
                        new Literal(enumDecl.getTypeName(), t.getTo().iterator().next().getName())));
                //TODO assert t.getTo().size() == 1
                _ifguard.addGuardedCommand(t.getGuard(), then);
                sl.add(_ifguard);
            });

            //transit
            checkForTransit = new IfStatement();
            StatementList p0 = new StatementList();
            checkForTransit.addGuardedCommand(new SymbolicReference(transitVariable), p0);
            for (SFCStep.AssociatedAction aa : step.getEvents()) {
                if (aa.getQualifier().getQualifier() == SFCActionQualifier.Qualifier.FALLING) {
                    p1.add(new InvocationStatement(aa.getActionName())); // actions allowed
                }
            }
        }
    }

    private void addActions(StatementList list,
                            List<SFCStep.AssociatedAction> events,
                            SFCActionQualifier.Qualifier... qualifiers) {
/*        EnumSet q = EnumSet.of(qualifiers[0], qualifiers);
        for (SFCStep.AssociatedAction aa : events) {
            if (q.contains(aa.getQualifier())) {
                if (scope.hasVariable(aa.getActionName())) {
                    //switch ()


                }
            }
        }*/
    }

    private void embeddSFCReset() {
        //todo add SFCReset:bool to scope
        //todo add IF SFCReset THEN _state = <init>
    }


    private void addVariables() {
        stateVariable = "_" + name + "_state";
        transitVariable = "_" + name + "_transit";

        scope.builder().identifiers(stateVariable)
                .type(enumDecl)
                .setInitialization(new IdentifierInitializer(network.getInitialStep().getName()))
                .close();

        scope.builder().identifiers(transitVariable)
                .boolType()
                .setInitialization(Literal.FALSE)
                .close();
    }

    private void extractStates() {
        enumDecl.setTypeName(name + "_states_t");
        enumDecl.getAllowedValues().add(
                new CommonToken(IEC61131Lexer.IDENTIFIER, network.getInitialStep().getName()));
        for (SFCStep step : network.getSteps()) {
            if (network.getInitialStep() == step)
                continue;
            enumDecl.getAllowedValues().add(
                    new CommonToken(IEC61131Lexer.IDENTIFIER, step.getName()));
        }
    }
}
