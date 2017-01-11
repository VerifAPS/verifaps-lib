package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import edu.kit.iti.formal.stvs.model.table.Commentable;
import edu.kit.iti.formal.stvs.model.table.StringEditable;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintCell implements CellOperationProvider {

    private Expression expression;
    private String userInputString;
    private String comment;

    private List<Consumer<Expression>> expressionListeners;
    private List<Consumer<String>> userInputStringListeners;

    public ConstraintCell(String userInputString) {
        this.userInputString = userInputString;
    }

    public Expression getExpression() {
        return expression;
    }


    @Override
    public String getUserInputString() {
        return userInputString;
    }

    @Override
    public void setUserInputString(String userInputString) {
        this.userInputString = userInputString;
    }

    public void addExpressionListener(Consumer<Expression> listener) {

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
