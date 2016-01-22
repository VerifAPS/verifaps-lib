package edu.kit.iti.formal.automation.sfclang.ast;

import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;
import edu.kit.iti.formal.automation.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.ast.Statement;
import edu.kit.iti.formal.automation.ast.StatementList;
import edu.kit.iti.formal.automation.ast.VariableScope;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collector;
import java.util.stream.Collectors;

/**
 * Top-Level Declaration for a Sequential Function Chart,
 * containing steps, actions, transitions, variables declaration.
 */
public class SFCDeclaration {

    private VariableScope scope = new VariableScope();
    private String name;
    private List<StepDeclaration> steps = new LinkedList<>();
    private List<FunctionBlockDeclaration> actions = new LinkedList<>();
    private List<TransitionDeclaration> transitions = new LinkedList<>();

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

    public VariableScope getScope() {
        return scope;
    }

    public void setScope(VariableScope scope) {
        this.scope = scope;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
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
        return name;
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
}
