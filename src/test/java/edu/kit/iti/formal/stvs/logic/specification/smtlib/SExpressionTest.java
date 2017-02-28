package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Test;

/**
 * Created by csicar on 08.02.17.
 */
public class SExpressionTest {
  @Test
  public void testSExpr() {
    SExpression e = new SList("asd", "asdd");
    System.out.println(e.toString());
  }

  @Test
  public void testSMTLIb() {
    //(assert (= (x 1) (y 1)))
    SExpression e = new SList("assert", new SList("=", new SList("x", "1"),
        new SList("y", "1")));

    System.out.println(e.toString());
  }
}