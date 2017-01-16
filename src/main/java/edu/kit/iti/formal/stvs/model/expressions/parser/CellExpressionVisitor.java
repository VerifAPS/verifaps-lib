package edu.kit.iti.formal.stvs.model.expressions.parser;// Generated from /home/philipp/program/PSE/stverificationstudio/CellExpression.g4 by ANTLR 4.6


import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link CellExpressionParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface CellExpressionVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#cell}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCell(CellExpressionParser.CellContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#chunk}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitChunk(CellExpressionParser.ChunkContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#dontcare}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDontcare(CellExpressionParser.DontcareContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#constant}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstant(CellExpressionParser.ConstantContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#singlesided}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSinglesided(CellExpressionParser.SinglesidedContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#interval}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInterval(CellExpressionParser.IntervalContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#relational_operator}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRelational_operator(CellExpressionParser.Relational_operatorContext ctx);
	/**
	 * Visit a parse tree produced by the {@code minus}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMinus(CellExpressionParser.MinusContext ctx);
	/**
	 * Visit a parse tree produced by the {@code negation}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNegation(CellExpressionParser.NegationContext ctx);
	/**
	 * Visit a parse tree produced by the {@code parens}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParens(CellExpressionParser.ParensContext ctx);
	/**
	 * Visit a parse tree produced by the {@code compare}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCompare(CellExpressionParser.CompareContext ctx);
	/**
	 * Visit a parse tree produced by the {@code mod}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMod(CellExpressionParser.ModContext ctx);
	/**
	 * Visit a parse tree produced by the {@code mult}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMult(CellExpressionParser.MultContext ctx);
	/**
	 * Visit a parse tree produced by the {@code binguardedCommand}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinguardedCommand(CellExpressionParser.BinguardedCommandContext ctx);
	/**
	 * Visit a parse tree produced by the {@code functioncall}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFunctioncall(CellExpressionParser.FunctioncallContext ctx);
	/**
	 * Visit a parse tree produced by the {@code bvariable}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBvariable(CellExpressionParser.BvariableContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logicalAnd}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalAnd(CellExpressionParser.LogicalAndContext ctx);
	/**
	 * Visit a parse tree produced by the {@code plus}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPlus(CellExpressionParser.PlusContext ctx);
	/**
	 * Visit a parse tree produced by the {@code div}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDiv(CellExpressionParser.DivContext ctx);
	/**
	 * Visit a parse tree produced by the {@code inequality}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInequality(CellExpressionParser.InequalityContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logicalXor}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalXor(CellExpressionParser.LogicalXorContext ctx);
	/**
	 * Visit a parse tree produced by the {@code bconstant}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBconstant(CellExpressionParser.BconstantContext ctx);
	/**
	 * Visit a parse tree produced by the {@code logicalOr}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalOr(CellExpressionParser.LogicalOrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code equality}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitEquality(CellExpressionParser.EqualityContext ctx);
	/**
	 * Visit a parse tree produced by the {@code substract}
	 * labeled alternative in {@link CellExpressionParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubstract(CellExpressionParser.SubstractContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#variable}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVariable(CellExpressionParser.VariableContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#guardedcommand}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGuardedcommand(CellExpressionParser.GuardedcommandContext ctx);
	/**
	 * Visit a parse tree produced by {@link CellExpressionParser#fixed_interval}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFixed_interval(CellExpressionParser.Fixed_intervalContext ctx);
}