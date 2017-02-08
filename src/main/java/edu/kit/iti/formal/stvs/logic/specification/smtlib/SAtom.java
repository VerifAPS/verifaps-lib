package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;

/**
 * Created by csicar on 08.02.17.
 */
public class SAtom implements SExpr {
  private String string;
  public SAtom(String string) {
    this.string = string;
  }


  public SAtom(Sexp s) {
    this.string = s.toString();
  }


  @Override
  public boolean isAtom() {
    return true;
  }

  @Override
  public Sexp toSexpr() {
    return SexpFactory.newAtomicSexp(string);
  }

  public String toString() {
    return "SAtom("+string+")";
  }
}
