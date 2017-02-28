package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;

/**
 * Interface for al S-Expression compatible classes.
 *
 * @author
 */
public interface SExpression {

  /**
   * Creates an instance from a given string.
   *
   * @param string string to parse
   * @return instance which is represented by {@code string}
   */
  static SExpression fromString(String string) {
    try {
      Sexp s = SexpFactory.parse(string);
      return fromSexp(s);
    } catch (SexpParserException exception) {
      throw new IllegalArgumentException(exception.getMessage());
    }
  }


  /**
   * Creates an instance from a given {@link Sexp}.
   *
   * @param s sexp that should be converted
   * @return instance which is represented by {@code s}
   */
  static SExpression fromSexp(Sexp s) {
    if (s.isAtomic()) {
      return new SAtom(s);
    } else {
      return new SList(s);
    }
  }

  /**
   * Returns if instance is atomic.
   *
   * @return is atomic
   */
  boolean isAtom();

  /**
   * Convert to {@link Sexp}.
   *
   * @return converted expression
   */
  Sexp toSexpr();

  /**
   * SExpression's textual representation.
   *
   * @return string containing the sexpression
   */
  String toText();

}
