package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by csicar on 08.02.17.
 * @author Carsten Csiky
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
    return "" + string + "";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    SAtom sAtom = (SAtom) o;

    return string != null ? string.equals(sAtom.string) : sAtom.string == null;
  }


  @Override
  public int hashCode() {
    return string != null ? string.hashCode() : 0;
  }

  @Override
  public String toText() {
    return string;
  }

  @Override
  public <E> E visit(SExprVisitor<E> visitor) {
    return visitor.visit(this);
  }

  @Override
  public <E> List<E> visitChildren(SExprVisitor<E> visitor) {
    return new ArrayList<>();
  }
}
