package stverificationstudio.expressions;

public abstract class Expression {

	public abstract <R> R takeVisitor(ExpressionVisitor<R> visitor);
	
}
