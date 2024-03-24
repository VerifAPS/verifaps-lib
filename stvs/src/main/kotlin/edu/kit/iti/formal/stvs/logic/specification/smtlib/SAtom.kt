package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;

/**
 * Represents an {@link SExpression} that is an atomic element.
 *
 * @author Carsten Csiky
 */
public class SAtom implements SExpression {
  private String string;

  /**
   * Creates an atomic expression from string.
   *
   * @param string string to represent
   */
  public SAtom(String string) {
    this.string = string;
  }


  /**
   * Creates an atomic expression from S-Expression.
   *
   * @param s Expression
   */
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
    return "" + string + "";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SAtom atom = (SAtom) o;

    return string != null ? string.equals(atom.string) : atom.string == null;
  }


  @Override
  public int hashCode() {
    return string != null ? string.hashCode() : 0;
  }

  @Override
  public String toText() {
    return string;
  }

}
