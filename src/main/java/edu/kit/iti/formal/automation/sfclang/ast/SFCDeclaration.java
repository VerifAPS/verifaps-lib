package edu.kit.iti.formal.automation.sfclang.ast;

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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Top-Level Declaration for a Sequential Function Chart,
 * containing steps, actions, transitions, variables declaration.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SFCDeclaration extends TopLevelScopeElement {

    private List<StepDeclaration> steps = new LinkedList<>();
    private List<FunctionBlockDeclaration> actions = new LinkedList<>();
    private List<TransitionDeclaration> transitions = new LinkedList<>();
    private String name;

    /**
     * <p>Getter for the field <code>steps</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<StepDeclaration> getSteps() {
        return steps;
    }

    /**
     * <p>Setter for the field <code>steps</code>.</p>
     *
     * @param steps a {@link java.util.List} object.
     */
    public void setSteps(List<StepDeclaration> steps) {
        this.steps = steps;
    }

    /**
     * <p>Getter for the field <code>transitions</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<TransitionDeclaration> getTransitions() {
        return transitions;
    }

    /**
     * <p>Setter for the field <code>transitions</code>.</p>
     *
     * @param transition a {@link java.util.List} object.
     */
    public void setTransitions(List<TransitionDeclaration> transition) {
        this.transitions = transition;
    }

    /**
     * <p>getDeclaration.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<StepDeclaration> getDeclaration() {
        return steps;
    }

    /**
     * <p>setDeclaration.</p>
     *
     * @param declaration a {@link java.util.List} object.
     */
    public void setDeclaration(List<StepDeclaration> declaration) {
        this.steps = declaration;
    }

    /**
     * <p>Getter for the field <code>actions</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<FunctionBlockDeclaration> getActions() {
        return actions;
    }

    /**
     * <p>Setter for the field <code>actions</code>.</p>
     *
     * @param actions a {@link java.util.List} object.
     */
    public void setActions(List<FunctionBlockDeclaration> actions) {
        this.actions = actions;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return getBlockName();
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return null;
    }

    /**
     * <p>visit.</p>
     *
     * @param v a {@link edu.kit.iti.formal.automation.sfclang.SFCAstVisitor} object.
     * @param <T> a T object.
     * @return a T object.
     */
    public <T> T visit(SFCAstVisitor<T> v) {
        return v.visit(this);
    }

    /**
     * <p>getStep.</p>
     *
     * @param childName a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration} object.
     */
    public StepDeclaration getStep(String childName) {
        for (StepDeclaration declaration : getSteps())
            if (declaration.getName().equals(childName))
                return declaration;
        return null;
    }

    /**
     * <p>getTransitionsFrom.</p>
     *
     * @param step a {@link edu.kit.iti.formal.automation.sfclang.ast.StepDeclaration} object.
     * @return a {@link java.util.List} object.
     */
    public List<TransitionDeclaration> getTransitionsFrom(StepDeclaration step) {
        return getTransitions().stream().filter(
                (TransitionDeclaration t) ->
                        t.getFrom().contains(step.getName()))
                .collect(Collectors.toList());
    }

    /**
     * <p>getAction.</p>
     *
     * @param action a {@link java.lang.String} object.
     * @return a {@link java.util.Collection} object.
     */
    public Collection<? extends Statement> getAction(String action) {
        Optional<FunctionBlockDeclaration> fb = getActions().stream()
                .filter(a -> a.getFunctionBlockName().equals(action)).findFirst();

        if (fb.isPresent()) {
            return fb.get().getFunctionBody();
        } else {
            return new StatementList();
        }

    }

    /** {@inheritDoc} */
    @Override
    public String getBlockName() {
        return name;
    }

    /**
     * <p>setBlockName.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public void setBlockName(String name) {
        this.name = name;
    }

}
