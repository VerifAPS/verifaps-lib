package edu.kit.iti.formal.automation.sfclang.ast;

import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;

import java.util.*;

/**
 *
 *
 */
public class StepDeclaration {
    boolean initial;
    String name;
    Map<String, List<String>> events = new HashMap<>();


    public boolean isInitial() {
        return initial;
    }

    public Map<String, List<String>> getEvents() {
        return events;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public void push(String eventType, String actionName) {
        if (!events.containsKey(eventType)) {
            events.put(eventType, new ArrayList<>());
        }

        events.get(eventType).add(actionName);
    }

    public <T> T visit(SFCAstVisitor<T> v) {
        return v.visit(this);
    }

    public boolean isInitialStep() {
        return initial;
    }

    public void setInitial(boolean initial) {
        initial = initial;
    }
}
