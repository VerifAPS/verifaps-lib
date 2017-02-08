package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by csicar on 08.02.17.
 */
public class SExprTest {
  @Test
  public void testSExpr() {
    SExpr e = new SList("asd", "asdd");
    System.out.println(e.toString());
  }

  @Test
  public void testSMTLIb() {
    //(assert (= (x 1) (y 1)))
    SExpr e = new SList("assert", new SList("=", new SList("x", "1"),
        new SList("y", "1")));

    System.out.println(e.toString());
  }
}