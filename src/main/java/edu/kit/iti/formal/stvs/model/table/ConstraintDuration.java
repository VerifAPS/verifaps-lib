package edu.kit.iti.formal.stvs.model.table;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintDuration implements CellOperationProvider {

    private LowerBoundedInterval bounds;
    private String userInputString;
    private String comment;

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


    @Override
    public void setComment(String comment) {

    }

    @Override
    public String getComment() {
        return null;
    }

    @Override
    public void addCommentListener(Consumer<Commentable> consumer) {

    }
}
