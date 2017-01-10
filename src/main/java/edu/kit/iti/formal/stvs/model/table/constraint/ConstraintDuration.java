package edu.kit.iti.formal.stvs.model.table.constraint;

import edu.kit.iti.formal.stvs.model.table.StringEditable;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintDuration implements StringEditable {

    private LowerBoundedInterval bounds;
    private String userInputString;

    private List<Consumer<LowerBoundedInterval>> Listeners;

    public ConstraintDuration(LowerBoundedInterval bounds) {
        this.bounds = bounds;
    }

    public LowerBoundedInterval getBounds() {
        return bounds;
    }

    public void setBounds(LowerBoundedInterval bounds) {
        this.bounds = bounds;
    }
    @Override
    public String getUserInputString() {
        return this.userInputString;
    }

    @Override
    public void setUserInputString(String input) {
        this.userInputString = userInputString;
    }

    public void addBoundsListener(Consumer<LowerBoundedInterval> listener) {

    }

    @Override
    public void addUserInputStringListener(Consumer<String> listener) {

    }


}
