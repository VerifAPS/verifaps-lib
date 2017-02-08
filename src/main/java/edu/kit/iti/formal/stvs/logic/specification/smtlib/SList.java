package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpList;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by csicar on 08.02.17.
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
    this.sexp = new LinkedList<>();
    this.sexp.add(new SAtom(command));
    this.sexp.addAll(Arrays.asList(sexp));
  }

  public SList(Sexp exp) {
    sexp = new LinkedList<>();
    exp.forEach((sitem) -> {
      sexp.add(SExpr.fromSexp(sitem));
    });
  }

  @Override
  public boolean isAtom() {
    return false;
  }

  @Override
  public Sexp toSexpr() {
    Sexp exp = SexpFactory.newNonAtomicSexp();
    sexp.forEach((sitem) -> exp.add(sitem.toSexpr()));
    return exp;
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
    return "SList( " + getList().stream().map(Object::toString).collect(Collectors.joining
        (", "))
        + " )";
  }
}
