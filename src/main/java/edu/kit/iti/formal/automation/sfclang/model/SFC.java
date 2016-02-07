package edu.kit.iti.formal.automation.sfclang.model;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 22.01.16.
 */
public class SFC {
    public String name;
    public List<SFCStep> steps = new ArrayList<>();
    public List<SFCAction> actions = new ArrayList<>();

    public SFCStep getStep(String name) {
        return steps.stream().filter(
                (SFCStep step) -> step.name.equals(name)).findFirst().orElse(null);
    }

    public SFCAction getAction(String name) {
        return actions.stream().filter(
                (SFCAction a) -> a.name.equals(name)).findFirst().orElse(null);
    }

    public void addAction(SFCAction action) {
        actions.add(action);
    }
}
