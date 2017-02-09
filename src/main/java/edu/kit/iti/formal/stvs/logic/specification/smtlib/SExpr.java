package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;

/**
 * Created by csicar on 08.02.17.
 */
public interface SExpr {

  static SExpr fromString(String string) {
    try {
      Sexp s = SexpFactory.parse(string);
      return fromSexp(s);
    } catch (SexpParserException exception) {
      throw new IllegalArgumentException(exception.getMessage());
    }
  }

  static SExpr fromSexp(Sexp s) {
    if(s.isAtomic()) {
      return new SAtom(s);
    } else {
      return new SList(s);
    }
  }

  boolean isAtom();

  Sexp toSexpr();




}
