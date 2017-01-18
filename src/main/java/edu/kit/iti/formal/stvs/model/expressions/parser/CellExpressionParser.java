package edu.kit.iti.formal.stvs.model.expressions.parser;// Generated from /home/philipp/program/PSE/stverificationstudio/antlr/CellExpression.g4 by ANTLR 4.6


import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.ATN;
import org.antlr.v4.runtime.atn.ATNDeserializer;
import org.antlr.v4.runtime.atn.ParserATNSimulator;
import org.antlr.v4.runtime.atn.PredictionContextCache;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.List;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CellExpressionParser extends Parser {
  static {
    RuntimeMetaData.checkVersion("4.6", RuntimeMetaData.VERSION);
  }

  protected static final DFA[] _decisionToDFA;
  protected static final PredictionContextCache _sharedContextCache =
      new PredictionContextCache();
  public static final int
      T__0 = 1, AND = 2, ARROW_RIGHT = 3, COMMA = 4, DIV = 5, EQUALS = 6, GREATER_EQUALS = 7,
      GREATER_THAN = 8, LBRACKET = 9, LESS_EQUALS = 10, LESS_THAN = 11, LPAREN = 12, MINUS = 13,
      MOD = 14, MULT = 15, NOT = 16, NOT_EQUALS = 17, OR = 18, PLUS = 19, POWER = 20, RBRACKET = 21,
      RPAREN = 22, XOR = 23, IF = 24, FI = 25, ELSE = 26, GUARD = 27, T = 28, F = 29, IDENTIFIER = 30,
      FLOAT = 31, INTEGER = 32, WS = 33;
  public static final int
      RULE_cell = 0, RULE_chunk = 1, RULE_dontcare = 2, RULE_constant = 3, RULE_singlesided = 4,
      RULE_interval = 5, RULE_relational_operator = 6, RULE_expr = 7, RULE_variable = 8,
      RULE_guardedcommand = 9, RULE_fixed_interval = 10;
  public static final String[] ruleNames = {
      "cell", "chunk", "dontcare", "constant", "singlesided", "interval", "relational_operator",
      "expr", "variable", "guardedcommand", "fixed_interval"
  };

  private static final String[] _LITERAL_NAMES = {
      null, "'->'", null, "'=>'", "','", "'/'", "'='", "'>='", "'>'", "'['",
      "'<='", "'<'", "'('", "'-'", null, "'*'", null, null, null, "'+'", "'**'",
      "']'", "')'", null, "'if'", "'fi'", "'else'", "'::'"
  };
  private static final String[] _SYMBOLIC_NAMES = {
      null, null, "AND", "ARROW_RIGHT", "COMMA", "DIV", "EQUALS", "GREATER_EQUALS",
      "GREATER_THAN", "LBRACKET", "LESS_EQUALS", "LESS_THAN", "LPAREN", "MINUS",
      "MOD", "MULT", "NOT", "NOT_EQUALS", "OR", "PLUS", "POWER", "RBRACKET",
      "RPAREN", "XOR", "IF", "FI", "ELSE", "GUARD", "T", "F", "IDENTIFIER",
      "FLOAT", "INTEGER", "WS"
  };
  public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

  /**
   * @deprecated Use {@link #VOCABULARY} instead.
   */
  @Deprecated
  public static final String[] tokenNames;

  static {
    tokenNames = new String[_SYMBOLIC_NAMES.length];
    for (int i = 0; i < tokenNames.length; i++) {
      tokenNames[i] = VOCABULARY.getLiteralName(i);
      if (tokenNames[i] == null) {
        tokenNames[i] = VOCABULARY.getSymbolicName(i);
      }

      if (tokenNames[i] == null) {
        tokenNames[i] = "<INVALID>";
      }
    }
  }

  @Override
  @Deprecated
  public String[] getTokenNames() {
    return tokenNames;
  }

  @Override

  public Vocabulary getVocabulary() {
    return VOCABULARY;
  }

  @Override
  public String getGrammarFileName() {
    return "CellExpression.g4";
  }

  @Override
  public String[] getRuleNames() {
    return ruleNames;
  }

  @Override
  public String getSerializedATN() {
    return _serializedATN;
  }

  @Override
  public ATN getATN() {
    return _ATN;
  }

  public CellExpressionParser(TokenStream input) {
    super(input);
    _interp = new ParserATNSimulator(this, _ATN, _decisionToDFA, _sharedContextCache);
  }

  public static class CellContext extends ParserRuleContext {
    public List<ChunkContext> chunk() {
      return getRuleContexts(ChunkContext.class);
    }

    public ChunkContext chunk(int i) {
      return getRuleContext(ChunkContext.class, i);
    }

    public List<TerminalNode> COMMA() {
      return getTokens(CellExpressionParser.COMMA);
    }

    public TerminalNode COMMA(int i) {
      return getToken(CellExpressionParser.COMMA, i);
    }

    public CellContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_cell;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterCell(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitCell(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitCell(this);
      else return visitor.visitChildren(this);
    }
  }

  public final CellContext cell() throws RecognitionException {
    CellContext _localctx = new CellContext(_ctx, getState());
    enterRule(_localctx, 0, RULE_cell);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(22);
        chunk();
        setState(27);
        _errHandler.sync(this);
        _la = _input.LA(1);
        while (_la == COMMA) {
          {
            {
              setState(23);
              match(COMMA);
              setState(24);
              chunk();
            }
          }
          setState(29);
          _errHandler.sync(this);
          _la = _input.LA(1);
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class ChunkContext extends ParserRuleContext {
    public DontcareContext dontcare() {
      return getRuleContext(DontcareContext.class, 0);
    }

    public VariableContext variable() {
      return getRuleContext(VariableContext.class, 0);
    }

    public ConstantContext constant() {
      return getRuleContext(ConstantContext.class, 0);
    }

    public SinglesidedContext singlesided() {
      return getRuleContext(SinglesidedContext.class, 0);
    }

    public IntervalContext interval() {
      return getRuleContext(IntervalContext.class, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public ChunkContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_chunk;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterChunk(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitChunk(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitChunk(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ChunkContext chunk() throws RecognitionException {
    ChunkContext _localctx = new ChunkContext(_ctx, getState());
    enterRule(_localctx, 2, RULE_chunk);
    try {
      setState(36);
      _errHandler.sync(this);
      switch (getInterpreter().adaptivePredict(_input, 1, _ctx)) {
        case 1:
          enterOuterAlt(_localctx, 1);
        {
          setState(30);
          dontcare();
        }
        break;
        case 2:
          enterOuterAlt(_localctx, 2);
        {
          setState(31);
          variable();
        }
        break;
        case 3:
          enterOuterAlt(_localctx, 3);
        {
          setState(32);
          constant();
        }
        break;
        case 4:
          enterOuterAlt(_localctx, 4);
        {
          setState(33);
          singlesided();
        }
        break;
        case 5:
          enterOuterAlt(_localctx, 5);
        {
          setState(34);
          interval();
        }
        break;
        case 6:
          enterOuterAlt(_localctx, 6);
        {
          setState(35);
          expr(0);
        }
        break;
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class DontcareContext extends ParserRuleContext {
    public DontcareContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_dontcare;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterDontcare(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitDontcare(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitDontcare(this);
      else return visitor.visitChildren(this);
    }
  }

  public final DontcareContext dontcare() throws RecognitionException {
    DontcareContext _localctx = new DontcareContext(_ctx, getState());
    enterRule(_localctx, 4, RULE_dontcare);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(38);
        match(MINUS);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class ConstantContext extends ParserRuleContext {
    public Token a;

    public TerminalNode INTEGER() {
      return getToken(CellExpressionParser.INTEGER, 0);
    }

    public TerminalNode T() {
      return getToken(CellExpressionParser.T, 0);
    }

    public TerminalNode F() {
      return getToken(CellExpressionParser.F, 0);
    }

    public ConstantContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_constant;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterConstant(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitConstant(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitConstant(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ConstantContext constant() throws RecognitionException {
    ConstantContext _localctx = new ConstantContext(_ctx, getState());
    enterRule(_localctx, 6, RULE_constant);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(40);
        ((ConstantContext) _localctx).a = _input.LT(1);
        _la = _input.LA(1);
        if (!((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T) | (1L << F) | (1L << INTEGER))) != 0))) {
          ((ConstantContext) _localctx).a = (Token) _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class SinglesidedContext extends ParserRuleContext {
    public Relational_operatorContext op;

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public Relational_operatorContext relational_operator() {
      return getRuleContext(Relational_operatorContext.class, 0);
    }

    public SinglesidedContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_singlesided;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterSinglesided(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitSinglesided(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitSinglesided(this);
      else return visitor.visitChildren(this);
    }
  }

  public final SinglesidedContext singlesided() throws RecognitionException {
    SinglesidedContext _localctx = new SinglesidedContext(_ctx, getState());
    enterRule(_localctx, 8, RULE_singlesided);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(42);
        ((SinglesidedContext) _localctx).op = relational_operator();
        setState(43);
        expr(0);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class IntervalContext extends ParserRuleContext {
    public ExprContext lower;
    public ExprContext upper;

    public TerminalNode LBRACKET() {
      return getToken(CellExpressionParser.LBRACKET, 0);
    }

    public TerminalNode COMMA() {
      return getToken(CellExpressionParser.COMMA, 0);
    }

    public TerminalNode RBRACKET() {
      return getToken(CellExpressionParser.RBRACKET, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public IntervalContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_interval;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterInterval(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitInterval(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitInterval(this);
      else return visitor.visitChildren(this);
    }
  }

  public final IntervalContext interval() throws RecognitionException {
    IntervalContext _localctx = new IntervalContext(_ctx, getState());
    enterRule(_localctx, 10, RULE_interval);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(45);
        match(LBRACKET);
        setState(46);
        ((IntervalContext) _localctx).lower = expr(0);
        setState(47);
        match(COMMA);
        setState(48);
        ((IntervalContext) _localctx).upper = expr(0);
        setState(49);
        match(RBRACKET);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class Relational_operatorContext extends ParserRuleContext {
    public Token relOp;

    public TerminalNode GREATER_THAN() {
      return getToken(CellExpressionParser.GREATER_THAN, 0);
    }

    public TerminalNode GREATER_EQUALS() {
      return getToken(CellExpressionParser.GREATER_EQUALS, 0);
    }

    public TerminalNode LESS_THAN() {
      return getToken(CellExpressionParser.LESS_THAN, 0);
    }

    public TerminalNode LESS_EQUALS() {
      return getToken(CellExpressionParser.LESS_EQUALS, 0);
    }

    public TerminalNode EQUALS() {
      return getToken(CellExpressionParser.EQUALS, 0);
    }

    public TerminalNode NOT_EQUALS() {
      return getToken(CellExpressionParser.NOT_EQUALS, 0);
    }

    public Relational_operatorContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_relational_operator;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener)
        ((CellExpressionListener) listener).enterRelational_operator(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitRelational_operator(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitRelational_operator(this);
      else return visitor.visitChildren(this);
    }
  }

  public final Relational_operatorContext relational_operator() throws RecognitionException {
    Relational_operatorContext _localctx = new Relational_operatorContext(_ctx, getState());
    enterRule(_localctx, 12, RULE_relational_operator);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(51);
        ((Relational_operatorContext) _localctx).relOp = _input.LT(1);
        _la = _input.LA(1);
        if (!((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << EQUALS) | (1L << GREATER_EQUALS) | (1L << GREATER_THAN) | (1L << LESS_EQUALS) | (1L << LESS_THAN) | (1L << NOT_EQUALS))) != 0))) {
          ((Relational_operatorContext) _localctx).relOp = (Token) _errHandler.recoverInline(this);
        } else {
          if (_input.LA(1) == Token.EOF) matchedEOF = true;
          _errHandler.reportMatch(this);
          consume();
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class ExprContext extends ParserRuleContext {
    public ExprContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_expr;
    }

    public ExprContext() {
    }

    public void copyFrom(ExprContext ctx) {
      super.copyFrom(ctx);
    }
  }

  public static class MinusContext extends ExprContext {
    public ExprContext sub;

    public TerminalNode MINUS() {
      return getToken(CellExpressionParser.MINUS, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public MinusContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterMinus(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitMinus(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitMinus(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class NegationContext extends ExprContext {
    public ExprContext sub;

    public TerminalNode NOT() {
      return getToken(CellExpressionParser.NOT, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public NegationContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterNegation(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitNegation(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitNegation(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class ParensContext extends ExprContext {
    public ExprContext sub;

    public TerminalNode LPAREN() {
      return getToken(CellExpressionParser.LPAREN, 0);
    }

    public TerminalNode RPAREN() {
      return getToken(CellExpressionParser.RPAREN, 0);
    }

    public ExprContext expr() {
      return getRuleContext(ExprContext.class, 0);
    }

    public ParensContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterParens(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitParens(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitParens(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class CompareContext extends ExprContext {
    public ExprContext left;
    public Token op;
    public ExprContext right;

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public TerminalNode LESS_THAN() {
      return getToken(CellExpressionParser.LESS_THAN, 0);
    }

    public TerminalNode GREATER_THAN() {
      return getToken(CellExpressionParser.GREATER_THAN, 0);
    }

    public TerminalNode GREATER_EQUALS() {
      return getToken(CellExpressionParser.GREATER_EQUALS, 0);
    }

    public TerminalNode LESS_EQUALS() {
      return getToken(CellExpressionParser.LESS_EQUALS, 0);
    }

    public CompareContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterCompare(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitCompare(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitCompare(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class ModContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode MOD() {
      return getToken(CellExpressionParser.MOD, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public ModContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterMod(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitMod(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitMod(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class MultContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode MULT() {
      return getToken(CellExpressionParser.MULT, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public MultContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterMult(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitMult(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitMult(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class BinguardedCommandContext extends ExprContext {
    public GuardedcommandContext guardedcommand() {
      return getRuleContext(GuardedcommandContext.class, 0);
    }

    public BinguardedCommandContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterBinguardedCommand(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitBinguardedCommand(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitBinguardedCommand(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class FunctioncallContext extends ExprContext {
    public Token n;

    public TerminalNode LPAREN() {
      return getToken(CellExpressionParser.LPAREN, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public TerminalNode RPAREN() {
      return getToken(CellExpressionParser.RPAREN, 0);
    }

    public TerminalNode IDENTIFIER() {
      return getToken(CellExpressionParser.IDENTIFIER, 0);
    }

    public List<TerminalNode> COMMA() {
      return getTokens(CellExpressionParser.COMMA);
    }

    public TerminalNode COMMA(int i) {
      return getToken(CellExpressionParser.COMMA, i);
    }

    public FunctioncallContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterFunctioncall(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitFunctioncall(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitFunctioncall(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class BvariableContext extends ExprContext {
    public VariableContext variable() {
      return getRuleContext(VariableContext.class, 0);
    }

    public BvariableContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterBvariable(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitBvariable(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitBvariable(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class LogicalAndContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode AND() {
      return getToken(CellExpressionParser.AND, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public LogicalAndContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterLogicalAnd(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitLogicalAnd(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitLogicalAnd(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class PlusContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode PLUS() {
      return getToken(CellExpressionParser.PLUS, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public PlusContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterPlus(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitPlus(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitPlus(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class DivContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode DIV() {
      return getToken(CellExpressionParser.DIV, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public DivContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterDiv(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitDiv(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitDiv(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class InequalityContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode NOT_EQUALS() {
      return getToken(CellExpressionParser.NOT_EQUALS, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public InequalityContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterInequality(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitInequality(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitInequality(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class LogicalXorContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode XOR() {
      return getToken(CellExpressionParser.XOR, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public LogicalXorContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterLogicalXor(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitLogicalXor(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitLogicalXor(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class BconstantContext extends ExprContext {
    public ConstantContext constant() {
      return getRuleContext(ConstantContext.class, 0);
    }

    public BconstantContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterBconstant(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitBconstant(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitBconstant(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class LogicalOrContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode OR() {
      return getToken(CellExpressionParser.OR, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public LogicalOrContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterLogicalOr(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitLogicalOr(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitLogicalOr(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class EqualityContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode EQUALS() {
      return getToken(CellExpressionParser.EQUALS, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public EqualityContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterEquality(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitEquality(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitEquality(this);
      else return visitor.visitChildren(this);
    }
  }

  public static class SubstractContext extends ExprContext {
    public ExprContext left;
    public ExprContext right;

    public TerminalNode MINUS() {
      return getToken(CellExpressionParser.MINUS, 0);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public SubstractContext(ExprContext ctx) {
      copyFrom(ctx);
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterSubstract(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitSubstract(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitSubstract(this);
      else return visitor.visitChildren(this);
    }
  }

  public final ExprContext expr() throws RecognitionException {
    return expr(0);
  }

  private ExprContext expr(int _p) throws RecognitionException {
    ParserRuleContext _parentctx = _ctx;
    int _parentState = getState();
    ExprContext _localctx = new ExprContext(_ctx, _parentState);
    ExprContext _prevctx = _localctx;
    int _startState = 14;
    enterRecursionRule(_localctx, 14, RULE_expr, _p);
    int _la;
    try {
      int _alt;
      enterOuterAlt(_localctx, 1);
      {
        setState(77);
        _errHandler.sync(this);
        switch (getInterpreter().adaptivePredict(_input, 3, _ctx)) {
          case 1: {
            _localctx = new MinusContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;

            setState(54);
            match(MINUS);
            setState(55);
            ((MinusContext) _localctx).sub = expr(18);
          }
          break;
          case 2: {
            _localctx = new NegationContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(56);
            match(NOT);
            setState(57);
            ((NegationContext) _localctx).sub = expr(17);
          }
          break;
          case 3: {
            _localctx = new ParensContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(58);
            match(LPAREN);
            setState(59);
            ((ParensContext) _localctx).sub = expr(0);
            setState(60);
            match(RPAREN);
          }
          break;
          case 4: {
            _localctx = new BinguardedCommandContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(62);
            guardedcommand();
          }
          break;
          case 5: {
            _localctx = new FunctioncallContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(63);
            ((FunctioncallContext) _localctx).n = match(IDENTIFIER);
            setState(64);
            match(LPAREN);
            setState(65);
            expr(0);
            setState(70);
            _errHandler.sync(this);
            _la = _input.LA(1);
            while (_la == COMMA) {
              {
                {
                  setState(66);
                  match(COMMA);
                  setState(67);
                  expr(0);
                }
              }
              setState(72);
              _errHandler.sync(this);
              _la = _input.LA(1);
            }
            setState(73);
            match(RPAREN);
          }
          break;
          case 6: {
            _localctx = new BconstantContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(75);
            constant();
          }
          break;
          case 7: {
            _localctx = new BvariableContext(_localctx);
            _ctx = _localctx;
            _prevctx = _localctx;
            setState(76);
            variable();
          }
          break;
        }
        _ctx.stop = _input.LT(-1);
        setState(114);
        _errHandler.sync(this);
        _alt = getInterpreter().adaptivePredict(_input, 5, _ctx);
        while (_alt != 2 && _alt != org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER) {
          if (_alt == 1) {
            if (_parseListeners != null) triggerExitRuleEvent();
            _prevctx = _localctx;
            {
              setState(112);
              _errHandler.sync(this);
              switch (getInterpreter().adaptivePredict(_input, 4, _ctx)) {
                case 1: {
                  _localctx = new ModContext(new ExprContext(_parentctx, _parentState));
                  ((ModContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(79);
                  if (!(precpred(_ctx, 15))) throw new FailedPredicateException(this, "precpred(_ctx, 15)");
                  setState(80);
                  match(MOD);
                  setState(81);
                  ((ModContext) _localctx).right = expr(15);
                }
                break;
                case 2: {
                  _localctx = new DivContext(new ExprContext(_parentctx, _parentState));
                  ((DivContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(82);
                  if (!(precpred(_ctx, 14))) throw new FailedPredicateException(this, "precpred(_ctx, 14)");
                  setState(83);
                  match(DIV);
                  setState(84);
                  ((DivContext) _localctx).right = expr(14);
                }
                break;
                case 3: {
                  _localctx = new MultContext(new ExprContext(_parentctx, _parentState));
                  ((MultContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(85);
                  if (!(precpred(_ctx, 13))) throw new FailedPredicateException(this, "precpred(_ctx, 13)");
                  setState(86);
                  match(MULT);
                  setState(87);
                  ((MultContext) _localctx).right = expr(14);
                }
                break;
                case 4: {
                  _localctx = new SubstractContext(new ExprContext(_parentctx, _parentState));
                  ((SubstractContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(88);
                  if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
                  setState(89);
                  match(MINUS);
                  setState(90);
                  ((SubstractContext) _localctx).right = expr(13);
                }
                break;
                case 5: {
                  _localctx = new PlusContext(new ExprContext(_parentctx, _parentState));
                  ((PlusContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(91);
                  if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
                  setState(92);
                  match(PLUS);
                  setState(93);
                  ((PlusContext) _localctx).right = expr(12);
                }
                break;
                case 6: {
                  _localctx = new CompareContext(new ExprContext(_parentctx, _parentState));
                  ((CompareContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(94);
                  if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
                  setState(95);
                  ((CompareContext) _localctx).op = _input.LT(1);
                  _la = _input.LA(1);
                  if (!((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << GREATER_EQUALS) | (1L << GREATER_THAN) | (1L << LESS_EQUALS) | (1L << LESS_THAN))) != 0))) {
                    ((CompareContext) _localctx).op = (Token) _errHandler.recoverInline(this);
                  } else {
                    if (_input.LA(1) == Token.EOF) matchedEOF = true;
                    _errHandler.reportMatch(this);
                    consume();
                  }
                  setState(96);
                  ((CompareContext) _localctx).right = expr(11);
                }
                break;
                case 7: {
                  _localctx = new EqualityContext(new ExprContext(_parentctx, _parentState));
                  ((EqualityContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(97);
                  if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
                  setState(98);
                  match(EQUALS);
                  setState(99);
                  ((EqualityContext) _localctx).right = expr(10);
                }
                break;
                case 8: {
                  _localctx = new InequalityContext(new ExprContext(_parentctx, _parentState));
                  ((InequalityContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(100);
                  if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
                  setState(101);
                  match(NOT_EQUALS);
                  setState(102);
                  ((InequalityContext) _localctx).right = expr(9);
                }
                break;
                case 9: {
                  _localctx = new LogicalAndContext(new ExprContext(_parentctx, _parentState));
                  ((LogicalAndContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(103);
                  if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
                  setState(104);
                  match(AND);
                  setState(105);
                  ((LogicalAndContext) _localctx).right = expr(8);
                }
                break;
                case 10: {
                  _localctx = new LogicalOrContext(new ExprContext(_parentctx, _parentState));
                  ((LogicalOrContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(106);
                  if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
                  setState(107);
                  match(OR);
                  setState(108);
                  ((LogicalOrContext) _localctx).right = expr(7);
                }
                break;
                case 11: {
                  _localctx = new LogicalXorContext(new ExprContext(_parentctx, _parentState));
                  ((LogicalXorContext) _localctx).left = _prevctx;
                  pushNewRecursionContext(_localctx, _startState, RULE_expr);
                  setState(109);
                  if (!(precpred(_ctx, 5))) throw new FailedPredicateException(this, "precpred(_ctx, 5)");
                  setState(110);
                  match(XOR);
                  setState(111);
                  ((LogicalXorContext) _localctx).right = expr(6);
                }
                break;
              }
            }
          }
          setState(116);
          _errHandler.sync(this);
          _alt = getInterpreter().adaptivePredict(_input, 5, _ctx);
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      unrollRecursionContexts(_parentctx);
    }
    return _localctx;
  }

  public static class VariableContext extends ParserRuleContext {
    public TerminalNode IDENTIFIER() {
      return getToken(CellExpressionParser.IDENTIFIER, 0);
    }

    public TerminalNode LBRACKET() {
      return getToken(CellExpressionParser.LBRACKET, 0);
    }

    public TerminalNode INTEGER() {
      return getToken(CellExpressionParser.INTEGER, 0);
    }

    public TerminalNode RBRACKET() {
      return getToken(CellExpressionParser.RBRACKET, 0);
    }

    public VariableContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_variable;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterVariable(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitVariable(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitVariable(this);
      else return visitor.visitChildren(this);
    }
  }

  public final VariableContext variable() throws RecognitionException {
    VariableContext _localctx = new VariableContext(_ctx, getState());
    enterRule(_localctx, 16, RULE_variable);
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(117);
        match(IDENTIFIER);
        setState(121);
        _errHandler.sync(this);
        switch (getInterpreter().adaptivePredict(_input, 6, _ctx)) {
          case 1: {
            setState(118);
            match(LBRACKET);
            setState(119);
            match(INTEGER);
            setState(120);
            match(RBRACKET);
          }
          break;
        }
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class GuardedcommandContext extends ParserRuleContext {
    public ExprContext c;
    public ExprContext t;

    public TerminalNode IF() {
      return getToken(CellExpressionParser.IF, 0);
    }

    public TerminalNode FI() {
      return getToken(CellExpressionParser.FI, 0);
    }

    public List<TerminalNode> GUARD() {
      return getTokens(CellExpressionParser.GUARD);
    }

    public TerminalNode GUARD(int i) {
      return getToken(CellExpressionParser.GUARD, i);
    }

    public List<ExprContext> expr() {
      return getRuleContexts(ExprContext.class);
    }

    public ExprContext expr(int i) {
      return getRuleContext(ExprContext.class, i);
    }

    public GuardedcommandContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_guardedcommand;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterGuardedcommand(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitGuardedcommand(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitGuardedcommand(this);
      else return visitor.visitChildren(this);
    }
  }

  public final GuardedcommandContext guardedcommand() throws RecognitionException {
    GuardedcommandContext _localctx = new GuardedcommandContext(_ctx, getState());
    enterRule(_localctx, 18, RULE_guardedcommand);
    int _la;
    try {
      enterOuterAlt(_localctx, 1);
      {
        setState(123);
        match(IF);
        setState(129);
        _errHandler.sync(this);
        _la = _input.LA(1);
        do {
          {
            {
              setState(124);
              match(GUARD);
              setState(125);
              ((GuardedcommandContext) _localctx).c = expr(0);
              setState(126);
              match(T__0);
              setState(127);
              ((GuardedcommandContext) _localctx).t = expr(0);
            }
          }
          setState(131);
          _errHandler.sync(this);
          _la = _input.LA(1);
        } while (_la == GUARD);
        setState(133);
        match(FI);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public static class Fixed_intervalContext extends ParserRuleContext {
    public Token a;
    public Token b;
    public Token c;

    public TerminalNode MINUS() {
      return getToken(CellExpressionParser.MINUS, 0);
    }

    public TerminalNode LBRACKET() {
      return getToken(CellExpressionParser.LBRACKET, 0);
    }

    public TerminalNode COMMA() {
      return getToken(CellExpressionParser.COMMA, 0);
    }

    public TerminalNode RBRACKET() {
      return getToken(CellExpressionParser.RBRACKET, 0);
    }

    public List<TerminalNode> INTEGER() {
      return getTokens(CellExpressionParser.INTEGER);
    }

    public TerminalNode INTEGER(int i) {
      return getToken(CellExpressionParser.INTEGER, i);
    }

    public Fixed_intervalContext(ParserRuleContext parent, int invokingState) {
      super(parent, invokingState);
    }

    @Override
    public int getRuleIndex() {
      return RULE_fixed_interval;
    }

    @Override
    public void enterRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).enterFixed_interval(this);
    }

    @Override
    public void exitRule(ParseTreeListener listener) {
      if (listener instanceof CellExpressionListener) ((CellExpressionListener) listener).exitFixed_interval(this);
    }

    @Override
    public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
      if (visitor instanceof CellExpressionVisitor)
        return ((CellExpressionVisitor<? extends T>) visitor).visitFixed_interval(this);
      else return visitor.visitChildren(this);
    }
  }

  public final Fixed_intervalContext fixed_interval() throws RecognitionException {
    Fixed_intervalContext _localctx = new Fixed_intervalContext(_ctx, getState());
    enterRule(_localctx, 20, RULE_fixed_interval);
    int _la;
    try {
      setState(142);
      _errHandler.sync(this);
      switch (_input.LA(1)) {
        case MINUS:
          enterOuterAlt(_localctx, 1);
        {
          setState(135);
          match(MINUS);
        }
        break;
        case LBRACKET:
          enterOuterAlt(_localctx, 2);
        {
          setState(136);
          match(LBRACKET);
          setState(137);
          ((Fixed_intervalContext) _localctx).a = match(INTEGER);
          setState(138);
          match(COMMA);
          setState(139);
          ((Fixed_intervalContext) _localctx).b = _input.LT(1);
          _la = _input.LA(1);
          if (!(_la == MINUS || _la == INTEGER)) {
            ((Fixed_intervalContext) _localctx).b = (Token) _errHandler.recoverInline(this);
          } else {
            if (_input.LA(1) == Token.EOF) matchedEOF = true;
            _errHandler.reportMatch(this);
            consume();
          }
          setState(140);
          match(RBRACKET);
        }
        break;
        case INTEGER:
          enterOuterAlt(_localctx, 3);
        {
          setState(141);
          ((Fixed_intervalContext) _localctx).c = match(INTEGER);
        }
        break;
        default:
          throw new NoViableAltException(this);
      }
    } catch (RecognitionException re) {
      _localctx.exception = re;
      _errHandler.reportError(this, re);
      _errHandler.recover(this, re);
    } finally {
      exitRule();
    }
    return _localctx;
  }

  public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
    switch (ruleIndex) {
      case 7:
        return expr_sempred((ExprContext) _localctx, predIndex);
    }
    return true;
  }

  private boolean expr_sempred(ExprContext _localctx, int predIndex) {
    switch (predIndex) {
      case 0:
        return precpred(_ctx, 15);
      case 1:
        return precpred(_ctx, 14);
      case 2:
        return precpred(_ctx, 13);
      case 3:
        return precpred(_ctx, 12);
      case 4:
        return precpred(_ctx, 11);
      case 5:
        return precpred(_ctx, 10);
      case 6:
        return precpred(_ctx, 9);
      case 7:
        return precpred(_ctx, 8);
      case 8:
        return precpred(_ctx, 7);
      case 9:
        return precpred(_ctx, 6);
      case 10:
        return precpred(_ctx, 5);
    }
    return true;
  }

  public static final String _serializedATN =
      "\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3#\u0093\4\2\t\2\4" +
          "\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t" +
          "\13\4\f\t\f\3\2\3\2\3\2\7\2\34\n\2\f\2\16\2\37\13\2\3\3\3\3\3\3\3\3\3" +
          "\3\3\3\5\3\'\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3" +
          "\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\7\t" +
          "G\n\t\f\t\16\tJ\13\t\3\t\3\t\3\t\3\t\5\tP\n\t\3\t\3\t\3\t\3\t\3\t\3\t" +
          "\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3" +
          "\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\7\ts\n\t\f\t\16\tv\13\t\3\n\3\n" +
          "\3\n\3\n\5\n|\n\n\3\13\3\13\3\13\3\13\3\13\3\13\6\13\u0084\n\13\r\13\16" +
          "\13\u0085\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\5\f\u0091\n\f\3\f\2\3" +
          "\20\r\2\4\6\b\n\f\16\20\22\24\26\2\6\4\2\36\37\"\"\5\2\b\n\f\r\23\23\4" +
          "\2\t\n\f\r\4\2\17\17\"\"\u00a3\2\30\3\2\2\2\4&\3\2\2\2\6(\3\2\2\2\b*\3" +
          "\2\2\2\n,\3\2\2\2\f/\3\2\2\2\16\65\3\2\2\2\20O\3\2\2\2\22w\3\2\2\2\24" +
          "}\3\2\2\2\26\u0090\3\2\2\2\30\35\5\4\3\2\31\32\7\6\2\2\32\34\5\4\3\2\33" +
          "\31\3\2\2\2\34\37\3\2\2\2\35\33\3\2\2\2\35\36\3\2\2\2\36\3\3\2\2\2\37" +
          "\35\3\2\2\2 \'\5\6\4\2!\'\5\22\n\2\"\'\5\b\5\2#\'\5\n\6\2$\'\5\f\7\2%" +
          "\'\5\20\t\2& \3\2\2\2&!\3\2\2\2&\"\3\2\2\2&#\3\2\2\2&$\3\2\2\2&%\3\2\2" +
          "\2\'\5\3\2\2\2()\7\17\2\2)\7\3\2\2\2*+\t\2\2\2+\t\3\2\2\2,-\5\16\b\2-" +
          ".\5\20\t\2.\13\3\2\2\2/\60\7\13\2\2\60\61\5\20\t\2\61\62\7\6\2\2\62\63" +
          "\5\20\t\2\63\64\7\27\2\2\64\r\3\2\2\2\65\66\t\3\2\2\66\17\3\2\2\2\678" +
          "\b\t\1\289\7\17\2\29P\5\20\t\24:;\7\22\2\2;P\5\20\t\23<=\7\16\2\2=>\5" +
          "\20\t\2>?\7\30\2\2?P\3\2\2\2@P\5\24\13\2AB\7 \2\2BC\7\16\2\2CH\5\20\t" +
          "\2DE\7\6\2\2EG\5\20\t\2FD\3\2\2\2GJ\3\2\2\2HF\3\2\2\2HI\3\2\2\2IK\3\2" +
          "\2\2JH\3\2\2\2KL\7\30\2\2LP\3\2\2\2MP\5\b\5\2NP\5\22\n\2O\67\3\2\2\2O" +
          ":\3\2\2\2O<\3\2\2\2O@\3\2\2\2OA\3\2\2\2OM\3\2\2\2ON\3\2\2\2Pt\3\2\2\2" +
          "QR\f\21\2\2RS\7\20\2\2Ss\5\20\t\21TU\f\20\2\2UV\7\7\2\2Vs\5\20\t\20WX" +
          "\f\17\2\2XY\7\21\2\2Ys\5\20\t\20Z[\f\16\2\2[\\\7\17\2\2\\s\5\20\t\17]" +
          "^\f\r\2\2^_\7\25\2\2_s\5\20\t\16`a\f\f\2\2ab\t\4\2\2bs\5\20\t\rcd\f\13" +
          "\2\2de\7\b\2\2es\5\20\t\ffg\f\n\2\2gh\7\23\2\2hs\5\20\t\13ij\f\t\2\2j" +
          "k\7\4\2\2ks\5\20\t\nlm\f\b\2\2mn\7\24\2\2ns\5\20\t\top\f\7\2\2pq\7\31" +
          "\2\2qs\5\20\t\brQ\3\2\2\2rT\3\2\2\2rW\3\2\2\2rZ\3\2\2\2r]\3\2\2\2r`\3" +
          "\2\2\2rc\3\2\2\2rf\3\2\2\2ri\3\2\2\2rl\3\2\2\2ro\3\2\2\2sv\3\2\2\2tr\3" +
          "\2\2\2tu\3\2\2\2u\21\3\2\2\2vt\3\2\2\2w{\7 \2\2xy\7\13\2\2yz\7\"\2\2z" +
          "|\7\27\2\2{x\3\2\2\2{|\3\2\2\2|\23\3\2\2\2}\u0083\7\32\2\2~\177\7\35\2" +
          "\2\177\u0080\5\20\t\2\u0080\u0081\7\3\2\2\u0081\u0082\5\20\t\2\u0082\u0084" +
          "\3\2\2\2\u0083~\3\2\2\2\u0084\u0085\3\2\2\2\u0085\u0083\3\2\2\2\u0085" +
          "\u0086\3\2\2\2\u0086\u0087\3\2\2\2\u0087\u0088\7\33\2\2\u0088\25\3\2\2" +
          "\2\u0089\u0091\7\17\2\2\u008a\u008b\7\13\2\2\u008b\u008c\7\"\2\2\u008c" +
          "\u008d\7\6\2\2\u008d\u008e\t\5\2\2\u008e\u0091\7\27\2\2\u008f\u0091\7" +
          "\"\2\2\u0090\u0089\3\2\2\2\u0090\u008a\3\2\2\2\u0090\u008f\3\2\2\2\u0091" +
          "\27\3\2\2\2\13\35&HOrt{\u0085\u0090";
  public static final ATN _ATN =
      new ATNDeserializer().deserialize(_serializedATN.toCharArray());

  static {
    _decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
    for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
      _decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
    }
  }
}