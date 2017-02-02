package edu.kit.iti.formal.stvs.model.code;

import org.antlr.v4.runtime.ANTLRErrorListener;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.atn.ATNConfigSet;
import org.antlr.v4.runtime.dfa.DFA;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

/**
 * Created by Lukas on 30.01.2017.
 */
public class SyntaxErrorListener implements ANTLRErrorListener {
  private List<SyntaxError> syntaxErrors = new ArrayList<>();

  @Override
  public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
    syntaxErrors.add(new SyntaxError(e.getOffendingToken()));
  }

  public List<SyntaxError> getSyntaxErrors() {
    return syntaxErrors;
  }


  @Override
  public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {

  }

  @Override
  public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {

  }

  @Override
  public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {

  }
}
