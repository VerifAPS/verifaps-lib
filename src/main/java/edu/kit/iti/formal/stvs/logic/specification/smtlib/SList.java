package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Represents a S-Expression of form ( expr_1 expr_2 expr_3 ... expr_n)
 * @author Carsten Csiky
 */
public class SList implements SExpr {
  private List<SExpr> sexp;

  public SList(SExpr ... sexp) {
    this(Arrays.asList(sexp));
  }

  public SList(List<SExpr> sexp) {
    this.sexp = sexp;
  }

  public SList(String ... vals) {
    this(Arrays.stream(vals).map(SAtom::new).collect(Collectors.toList()));
  }

  public SList() {
    this(new LinkedList<SExpr>());
  }

  public SList(String command) {
    this(new LinkedList<SExpr>());
    addAll(command);
  }

  public SList(String command, SExpr ... sexp) {
    this();
    addAll(new SAtom(command));
    addAll(Arrays.asList(sexp));
  }

  public SList(Sexp exp) {
    sexp = new LinkedList<>();
    exp.forEach(this::addSexp);
  }

  private static void addItemToSexp(Sexp exp, SExpr sitem) {
    exp.add(sitem.toSexpr());
  }

  private void addSexp(Sexp sitem) {
    sexp.add(SExpr.fromSexp(sitem));
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
    return " ( " + getList().stream().map(SExpr::toText).collect(Collectors.joining(" ")) + " ) ";
  }


  @Override
  public <E> E visit(SExprVisitor<E> visitor) {
    return visitor.visit(this);
  }

  @Override
  public <E> List<E> visitChildren(SExprVisitor<E> visitor) {
    return getList().stream().map(visitor::visit).collect(Collectors.toList());
  }

  public SList addAll(SExpr ... sexp) {
    return  addAll(Arrays.asList(sexp));
  }

  public SList addAll(String ... values) {
    return addAll(Arrays.stream(values).map(SAtom::new).collect(Collectors.toList()));
  }

  public SList addListElements(List<String> values) {
    return addAll(values.stream().map(SAtom::new).collect(Collectors.toList()));
  }

  public SList addAll(List<SExpr> sExprs) {
    this.sexp.addAll(sExprs);
    return this;
  }

  public List<SExpr> getList() {
    return this.sexp;
  }

  public String toString() {
    return "( " + getList().stream().map(Object::toString).collect(Collectors.joining
        (" "))
        + " )";
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    SList sList = (SList) o;

    return sexp != null ? sexp.equals(sList.sexp) : sList.sexp == null;
  }

  @Override
  public int hashCode() {
    return sexp != null ? sexp.hashCode() : 0;
  }
}
