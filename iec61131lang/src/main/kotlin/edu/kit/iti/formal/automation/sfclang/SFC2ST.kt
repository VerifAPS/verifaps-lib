package edu.kit.iti.formal.automation.sfclang

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import com.google.common.collect.HashMultimap
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import lombok.Getter
import lombok.RequiredArgsConstructor
import lombok.Setter
import org.antlr.v4.runtime.CommonToken

import java.util.function.Supplier

/**
 * @author Alexander Weigl
 * @version 1 (23.02.18)
 */
@RequiredArgsConstructor
class SFC2ST : Supplier<StatementList> {
    private val name: String? = null
    @Getter
    val network: SFCNetwork? = null
    @Getter
    val scope: Scope? = null
    @Getter
    val stBody = StatementList()
    @Getter
    val enumDecl = EnumerationTypeDeclaration()
    @Getter
    @Setter
    var isSfcReset: Boolean = false
        set(sfcReset) {
            field = isSfcReset
        }
    private var stateVariable: String? = null
    private var transitVariable: String? = null

    override fun get(): StatementList {
        extractStates()
        addVariables()
        //actionAnalyses();
        addNonStoredVariablesReset() // all non-stored assignments are reseted

        //code
        if (isSfcReset) {
            embeddSFCReset()
        }

        createBigCase()
        return stBody
    }

    private fun actionAnalyses() {
        //System.out.println(name);
        val actionMap = HashMultimap.create<String, SFCActionQualifier.Qualifier>()
        network!!.steps.stream().flatMap<SFCStep.AssociatedAction> { s -> s.events.stream() }
                .filter { aa -> scope!!.hasVariable(aa.actionName) }
                .forEach { aa -> actionMap.put(aa.actionName, aa.qualifier!!.qualifier) }
        println(actionMap)

        /*network.getSteps().stream().flatMap(s -> s.getOutgoing().stream())
                .filter(t -> t.getFrom().size()>1|| t.getTo().size()>1)
                //.forEach(t -> System.out.format("%d => %d%n", t.getFrom().size(), t.getTo().size()));
                .forEach(t -> System.out.format("%s => %s%n",
                        t.getFrom().stream().map(s->s.getName()).collect(Collectors.joining(",")),
                        t.getTo().stream().map(s->s.getName()).collect(Collectors.joining(","))));
        */
    }

    private fun addNonStoredVariablesReset() {
        network!!.steps.stream().flatMap<SFCStep.AssociatedAction> { s -> s.events.stream() }
                .filter { aa -> aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.NON_STORED }
                .filter { aa -> scope!!.hasVariable(aa.actionName) }
                .forEach { aa ->
                    stBody.add(AssignmentStatement(
                            SymbolicReference(aa.actionName),
                            Literal.FALSE
                    ))
                }
    }

    private fun createBigCase() {
        val statement = CaseStatement()
        statement.expression = SymbolicReference(stateVariable)
        stBody.add(statement)

        for (step in network!!.steps) {
            val _case = Case()
            val cc = CaseCondition.Enumeration(
                    Literal(enumDecl.name, step.name))
            _case.conditions = arrayListOf(cc)
            statement.addCase(_case)
            val sl = _case.statements

            //transit
            var checkForTransit = IfStatement()
            val p1 = StatementList()
            checkForTransit.addGuardedCommand(SymbolicReference(transitVariable), p1)
            for (aa in step.events) {
                if (aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.RAISING) {
                    p1.add(InvocationStatement(aa.actionName)) // actions allowed
                }
            }
            if (p1.size > 0) {
                sl.add(checkForTransit)
            }
            sl.add(AssignmentStatement(SymbolicReference(transitVariable), Literal.FALSE))

            // S+N, R
            step.events.stream().filter { aa -> aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.SET || aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.NON_STORED }
                    .forEach { aa ->
                        if (scope!!.hasVariable(aa.actionName)) {
                            sl.add(AssignmentStatement(SymbolicReference(aa.actionName), Literal.TRUE))
                        } else {
                            sl.add(InvocationStatement(aa.actionName))
                        }
                    }
            step.events.stream().filter { aa -> aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.OVERRIDING_RESET }
                    .forEach { aa ->
                        if (scope!!.hasVariable(aa.actionName)) {
                            sl.add(AssignmentStatement(SymbolicReference(aa.actionName), Literal.FALSE))
                        } else {
                            //Not handled!
                        }
                    }

            // outgoing transition
            step.outgoing.sortWith(SFCTransition.PriorityComparison())
            step.outgoing.forEach { t ->
                val _ifguard = IfStatement()
                val then = StatementList()
                then.add(AssignmentStatement(SymbolicReference(transitVariable), Literal.TRUE))
                then.add(AssignmentStatement(SymbolicReference(stateVariable),
                        Literal(enumDecl.name, t.to!!.iterator().next().name)))
                //TODO assert t.getTo().size() == 1
                _ifguard.addGuardedCommand(t.guard, then)
                sl.add(_ifguard)
            }

            //transit
            checkForTransit = IfStatement()
            val p0 = StatementList()
            checkForTransit.addGuardedCommand(SymbolicReference(transitVariable), p0)
            for (aa in step.events) {
                if (aa.qualifier!!.qualifier == SFCActionQualifier.Qualifier.FALLING) {
                    p1.add(InvocationStatement(aa.actionName)) // actions allowed
                }
            }
        }
    }

    private fun addActions(list: StatementList,
                           events: List<SFCStep.AssociatedAction>,
                           vararg qualifiers: SFCActionQualifier.Qualifier) {
        /*        EnumSet q = EnumSet.of(qualifiers[0], qualifiers);
        for (SFCStep.AssociatedAction aa : events) {
            if (q.contains(aa.getQualifier())) {
                if (scope.hasVariable(aa.getActionName())) {
                    //switch ()


                }
            }
        }*/
    }

    private fun embeddSFCReset() {
        //todo add SFCReset:bool to scope
        //todo add IF SFCReset THEN _state = <init>
    }


    private fun addVariables() {
        stateVariable = "_" + name + "_state"
        transitVariable = "_" + name + "_transit"

        scope!!.builder().identifiers(stateVariable!!)
                .type(enumDecl)
                .setInitialization(IdentifierInitializer(null, network!!.initialStep!!.name))
                .close()

        scope.builder().identifiers(transitVariable!!)
                .boolType()
                .setInitialization(Literal.FALSE)
                .close()
    }

    private fun extractStates() {
        enumDecl.name = name!! + "_states_t"
        enumDecl.allowedValues.add(
                CommonToken(IEC61131Lexer.IDENTIFIER, network!!.initialStep!!.name))
        for (step in network.steps) {
            if (network.initialStep === step)
                continue
            enumDecl.allowedValues.add(
                    CommonToken(IEC61131Lexer.IDENTIFIER, step.name))
        }
    }
}
