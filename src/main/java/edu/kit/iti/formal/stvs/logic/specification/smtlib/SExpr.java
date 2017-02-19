package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;

import java.util.List;
import java.util.function.Function;

/**
 * Created by csicar on 08.02.17.
 * @author
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

  /**
   * SExpression's textual representation
   * @return string containing the sexpression
   */
  String toText();

  /**
   * does the SExpr contain the given sexpr?
   * @param expr expression to check for
   * @return true, if SExpr is contained
   */
  default boolean contains(SExpr expr) {
    return this.visit(c ->
        c.equals(expr) || c.visitChildren(this::contains).stream().anyMatch(e
        -> true));
  }

  <E> E visit(Function<? super SExpr, E> visitor);

  <E> List<E> visitChildren(Function<? super SExpr, E> visitor);

}
