package edu.kit.iti.formal.stvs.model.expressions.parser;// Generated from /home/philipp/program/PSE/stverificationstudio/antlr/CellExpression.g4 by ANTLR 4.6


import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link CellExpressionParser}.
 */
public interface CellExpressionListener extends ParseTreeListener {
  /**
   * Enter a parse tree produced by {@link CellExpressionParser#cell}.
   *
   * @param ctx the parse tree
   */
  void enterCell(CellExpressionParser.CellContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#cell}.
   *
   * @param ctx the parse tree
   */
  void exitCell(CellExpressionParser.CellContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#chunk}.
   *
   * @param ctx the parse tree
   */
  void enterChunk(CellExpressionParser.ChunkContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#chunk}.
   *
   * @param ctx the parse tree
   */
  void exitChunk(CellExpressionParser.ChunkContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#dontcare}.
   *
   * @param ctx the parse tree
   */
  void enterDontcare(CellExpressionParser.DontcareContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#dontcare}.
   *
   * @param ctx the parse tree
   */
  void exitDontcare(CellExpressionParser.DontcareContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#constant}.
   *
   * @param ctx the parse tree
   */
  void enterConstant(CellExpressionParser.ConstantContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#constant}.
   *
   * @param ctx the parse tree
   */
  void exitConstant(CellExpressionParser.ConstantContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#singlesided}.
   *
   * @param ctx the parse tree
   */
  void enterSinglesided(CellExpressionParser.SinglesidedContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#singlesided}.
   *
   * @param ctx the parse tree
   */
  void exitSinglesided(CellExpressionParser.SinglesidedContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#interval}.
   *
   * @param ctx the parse tree
   */
  void enterInterval(CellExpressionParser.IntervalContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#interval}.
   *
   * @param ctx the parse tree
   */
  void exitInterval(CellExpressionParser.IntervalContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#relational_operator}.
   *
   * @param ctx the parse tree
   */
  void enterRelational_operator(CellExpressionParser.Relational_operatorContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#relational_operator}.
   *
   * @param ctx the parse tree
   */
  void exitRelational_operator(CellExpressionParser.Relational_operatorContext ctx);

  /**
   * Enter a parse tree produced by the {@code minus}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterMinus(CellExpressionParser.MinusContext ctx);

  /**
   * Exit a parse tree produced by the {@code minus}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitMinus(CellExpressionParser.MinusContext ctx);

  /**
   * Enter a parse tree produced by the {@code negation}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterNegation(CellExpressionParser.NegationContext ctx);

  /**
   * Exit a parse tree produced by the {@code negation}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitNegation(CellExpressionParser.NegationContext ctx);

  /**
   * Enter a parse tree produced by the {@code parens}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterParens(CellExpressionParser.ParensContext ctx);

  /**
   * Exit a parse tree produced by the {@code parens}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitParens(CellExpressionParser.ParensContext ctx);

  /**
   * Enter a parse tree produced by the {@code compare}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterCompare(CellExpressionParser.CompareContext ctx);

  /**
   * Exit a parse tree produced by the {@code compare}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitCompare(CellExpressionParser.CompareContext ctx);

  /**
   * Enter a parse tree produced by the {@code mod}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterMod(CellExpressionParser.ModContext ctx);

  /**
   * Exit a parse tree produced by the {@code mod}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitMod(CellExpressionParser.ModContext ctx);

  /**
   * Enter a parse tree produced by the {@code mult}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterMult(CellExpressionParser.MultContext ctx);

  /**
   * Exit a parse tree produced by the {@code mult}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitMult(CellExpressionParser.MultContext ctx);

  /**
   * Enter a parse tree produced by the {@code binguardedCommand}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterBinguardedCommand(CellExpressionParser.BinguardedCommandContext ctx);

  /**
   * Exit a parse tree produced by the {@code binguardedCommand}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitBinguardedCommand(CellExpressionParser.BinguardedCommandContext ctx);

  /**
   * Enter a parse tree produced by the {@code functioncall}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterFunctioncall(CellExpressionParser.FunctioncallContext ctx);

  /**
   * Exit a parse tree produced by the {@code functioncall}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitFunctioncall(CellExpressionParser.FunctioncallContext ctx);

  /**
   * Enter a parse tree produced by the {@code bvariable}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterBvariable(CellExpressionParser.BvariableContext ctx);

  /**
   * Exit a parse tree produced by the {@code bvariable}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitBvariable(CellExpressionParser.BvariableContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicalAnd}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterLogicalAnd(CellExpressionParser.LogicalAndContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicalAnd}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitLogicalAnd(CellExpressionParser.LogicalAndContext ctx);

  /**
   * Enter a parse tree produced by the {@code plus}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterPlus(CellExpressionParser.PlusContext ctx);

  /**
   * Exit a parse tree produced by the {@code plus}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitPlus(CellExpressionParser.PlusContext ctx);

  /**
   * Enter a parse tree produced by the {@code div}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterDiv(CellExpressionParser.DivContext ctx);

  /**
   * Exit a parse tree produced by the {@code div}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitDiv(CellExpressionParser.DivContext ctx);

  /**
   * Enter a parse tree produced by the {@code inequality}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterInequality(CellExpressionParser.InequalityContext ctx);

  /**
   * Exit a parse tree produced by the {@code inequality}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitInequality(CellExpressionParser.InequalityContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicalXor}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterLogicalXor(CellExpressionParser.LogicalXorContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicalXor}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitLogicalXor(CellExpressionParser.LogicalXorContext ctx);

  /**
   * Enter a parse tree produced by the {@code bconstant}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterBconstant(CellExpressionParser.BconstantContext ctx);

  /**
   * Exit a parse tree produced by the {@code bconstant}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitBconstant(CellExpressionParser.BconstantContext ctx);

  /**
   * Enter a parse tree produced by the {@code logicalOr}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterLogicalOr(CellExpressionParser.LogicalOrContext ctx);

  /**
   * Exit a parse tree produced by the {@code logicalOr}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitLogicalOr(CellExpressionParser.LogicalOrContext ctx);

  /**
   * Enter a parse tree produced by the {@code equality}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterEquality(CellExpressionParser.EqualityContext ctx);

  /**
   * Exit a parse tree produced by the {@code equality}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitEquality(CellExpressionParser.EqualityContext ctx);

  /**
   * Enter a parse tree produced by the {@code substract}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void enterSubstract(CellExpressionParser.SubstractContext ctx);

  /**
   * Exit a parse tree produced by the {@code substract}
   * labeled alternative in {@link CellExpressionParser#expr}.
   *
   * @param ctx the parse tree
   */
  void exitSubstract(CellExpressionParser.SubstractContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#variable}.
   *
   * @param ctx the parse tree
   */
  void enterVariable(CellExpressionParser.VariableContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#variable}.
   *
   * @param ctx the parse tree
   */
  void exitVariable(CellExpressionParser.VariableContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#guardedcommand}.
   *
   * @param ctx the parse tree
   */
  void enterGuardedcommand(CellExpressionParser.GuardedcommandContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#guardedcommand}.
   *
   * @param ctx the parse tree
   */
  void exitGuardedcommand(CellExpressionParser.GuardedcommandContext ctx);

  /**
   * Enter a parse tree produced by {@link CellExpressionParser#fixed_interval}.
   *
   * @param ctx the parse tree
   */
  void enterFixed_interval(CellExpressionParser.Fixed_intervalContext ctx);

  /**
   * Exit a parse tree produced by {@link CellExpressionParser#fixed_interval}.
   *
   * @param ctx the parse tree
   */
  void exitFixed_interval(CellExpressionParser.Fixed_intervalContext ctx);
}