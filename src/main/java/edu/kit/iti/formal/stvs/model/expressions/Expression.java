package edu.kit.iti.formal.stvs.model.expressions;

public abstract class Expression {

    public abstract <R> R takeVisitor(ExpressionVisitor<R> visitor);

}
