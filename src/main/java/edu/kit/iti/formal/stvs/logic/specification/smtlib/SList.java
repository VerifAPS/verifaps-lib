package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Represents a S-Expression of form ( expr_1 expr_2 expr_3 ... expr_n)
 *
 * @author Carsten Csiky
 */
public class SList implements SExpression {
  private List<SExpression> sexp;

  /**
   * Creates an instance from a list of {@link SExpression}.
   * if the passed list must be modifiable for the methods add() and allAll() to work properly
   * @param sexp list of {@link SExpression}
   */
  public SList(List<SExpression> sexp) {
    this.sexp = sexp;
  }

  /**
   * Helper constructor. Creates a {@link SAtom} for any passed string an calls
   * {@link SList#SList(List)}
   *
   * @param vals atomic expressions as string
   */
  public SList(String... vals) {
    this(Arrays.stream(vals).map(SAtom::new).collect(Collectors.toList()));
  }

  /**
   * Creates an empty SList.
   */
  public SList() {
    this(new LinkedList<SExpression>());
  }

  public SList(String command) {
    this(new LinkedList<SExpression>());
    addAll(command);
  }

  /**
   * Creates an SList with the first argument interpreted as atomic expression followed by
   * {@code sexp}.
   *
   * @param command atomic command expression
   * @param sexp following expressions
   */
  public SList(String command, SExpression... sexp) {
    this();
    addAll(new SAtom(command));
    addAll(Arrays.asList(sexp));
  }

  /**
   * Creates an instance by using an {@link Sexp} as a base. Every item in {@code exp} will become
   * an item in this list.
   *
   * @param exp base expression
   */
  public SList(Sexp exp) {
    sexp = new LinkedList<>();
    exp.forEach(this::addSexp);
  }

  private static void addItemToSexp(Sexp exp, SExpression sitem) {
    exp.add(sitem.toSexpr());
  }

  private void addSexp(Sexp sitem) {
    sexp.add(SExpression.fromSexp(sitem));
  }

  @Override
  public boolean isAtom() {
    return false;
  }

  @Override
  public Sexp toSexpr() {
    Sexp exp = SexpFactory.newNonAtomicSexp();
    sexp.forEach((sitem) -> addItemToSexp(exp, sitem));
    return exp;
  }

  @Override
  public String toText() {
    return " ( " + getList().stream().map(SExpression::toText).collect(Collectors.joining(" "))
        + " ) ";
  }

  public SList addAll(SExpression... sexp) {
    return addAll(Arrays.asList(sexp));
  }

  public SList addAll(String... values) {
    return addAll(Arrays.stream(values).map(SAtom::new).collect(Collectors.toList()));
  }

  public SList addAll(List<SExpression> exprs) {
    this.sexp.addAll(exprs);
    return this;
  }

  public SList addListElements(List<String> values) {
    return addAll(values.stream().map(SAtom::new).collect(Collectors.toList()));
  }

  public List<SExpression> getList() {
    return this.sexp;
  }

  /**
   * Returns the List as a string
   *
   * @return string representation: "(item_1 item_2 ... item_n)"
   */
  public String toString() {
    return "( " + getList().stream().map(Object::toString).collect(Collectors.joining(" ")) + " )";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SList list = (SList) o;

    return sexp != null ? sexp.equals(list.sexp) : list.sexp == null;
  }

  @Override
  public int hashCode() {
    return sexp != null ? sexp.hashCode() : 0;
  }
}
