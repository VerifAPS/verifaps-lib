package edu.kit.iti.formal.stvs.model.expressions.parser;

import org.antlr.v4.runtime.ANTLRErrorListener;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;

import java.util.BitSet;

/**
 * A {@link ThrowingErrorListener} that throws {@link ParseRuntimeException}s on
 * every syntaxError.
 * @author Philipp
 */
public class ThrowingErrorListener implements ANTLRErrorListener {
  @Override
  public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
    throw new ParseRuntimeException(new ParseException(line, charPositionInLine, msg));
  }

  @Override
  public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {
    // we can _prooobably_ just ignore these (parses successfully even though this is invoked.)
  }

  @Override
  public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {
    // same
  }

  @Override
  public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {
    // never got this call in all tests.
  }
}
