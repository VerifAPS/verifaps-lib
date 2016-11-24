package edu.kit.iti.formal.automation.sfclang.ast;

import edu.kit.iti.formal.automation.LocalScope;
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
 */
public class SFCDeclaration extends TopLevelScopeElement {

    private List<StepDeclaration> steps = new LinkedList<>();
    private List<FunctionBlockDeclaration> actions = new LinkedList<>();
    private List<TransitionDeclaration> transitions = new LinkedList<>();
    private String name;

    public List<StepDeclaration> getSteps() {
        return steps;
    }

    public void setSteps(List<StepDeclaration> steps) {
        this.steps = steps;
    }

    public List<TransitionDeclaration> getTransitions() {
        return transitions;
    }

    public void setTransitions(List<TransitionDeclaration> transition) {
        this.transitions = transition;
    }

    public List<StepDeclaration> getDeclaration() {
        return steps;
    }

    public void setDeclaration(List<StepDeclaration> declaration) {
        this.steps = declaration;
    }

    public List<FunctionBlockDeclaration> getActions() {
        return actions;
    }

    public void setActions(List<FunctionBlockDeclaration> actions) {
        this.actions = actions;
    }

    @Override
    public String toString() {
        return getBlockName();
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return null;
    }

    public <T> T visit(SFCAstVisitor<T> v) {
        return v.visit(this);
    }

    public StepDeclaration getStep(String childName) {
        for (StepDeclaration declaration : getSteps())
            if (declaration.getName().equals(childName))
                return declaration;
        return null;
    }

    public List<TransitionDeclaration> getTransitionsFrom(StepDeclaration step) {
        return getTransitions().stream().filter(
                (TransitionDeclaration t) ->
                        t.getFrom().contains(step.getName()))
                .collect(Collectors.toList());
    }

    public Collection<? extends Statement> getAction(String action) {
        Optional<FunctionBlockDeclaration> fb = getActions().stream()
                .filter(a -> a.getFunctionBlockName().equals(action)).findFirst();

        if (fb.isPresent()) {
            return fb.get().getFunctionBody();
        } else {
            return new StatementList();
        }

    }

    @Override
    public String getBlockName() {
        return name;
    }

    public void setBlockName(String name) {
        this.name = name;
    }

}
