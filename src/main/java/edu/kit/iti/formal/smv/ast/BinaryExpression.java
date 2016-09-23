package edu.kit.iti.formal.smv.ast;

import edu.kit.iti.formal.smv.ast.Expression;

/************************************************************/
/**
 * 
 */
public class BinaryExpression extends Expression {
	/**
	 * 
	 */
	public Expression left;

	/**
	 * 
	 */
	public Expression right;

	/**
	 * 
	 */
	public BinaryOperator operator;

	@Override
	public DataType getDataType() {
		return DataType.infer(left.getDataType(), right.getDataType());
	}
};
