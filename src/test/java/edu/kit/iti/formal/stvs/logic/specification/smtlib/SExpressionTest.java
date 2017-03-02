package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;

/**
 * Created by csicar on 08.02.17.
 */
@RunWith(Parameterized.class)
public class SExpressionTest {
  public SExpression expression;


  public SExpressionTest(SExpression expression) {
    this.expression = expression;
  }

  @Parameterized.Parameters
  public static Collection<Object[]> instancesToTest() {
    SList list = new SList("a", new SAtom("b"), new SAtom("c"), new SList("n1", "n2"));
    return Arrays.asList(
        new Object[]{list},
        new Object[]{new SAtom("asdasd")},
        new Object[]{new SAtom("1")}
    );
  }

  @Test
  public void fromString() throws Exception {
    assertEquals(
        new SList("a", new SAtom("b"), new SAtom("c"),
            new SList("nested1", "2", "3"),
            new SList("4")),
        SExpression.fromText("(a b c (nested1 2 3 ) (4))"));
  }

  @Test(expected = IllegalArgumentException.class)
  public void fromStringWrongInput() {
    SExpression.fromText(")asdasd");
  }

  @Test
  public void fromSexp() throws Exception {
    assertEquals(expression, SExpression.fromSexp(expression.toSexpr()));
  }

  @Test
  public void isAtom() throws Exception {
    assertEquals(expression.toSexpr().isAtomic(), expression.isAtom());
  }

  @Test
  public void toText() throws Exception {
    assertEquals(expression, SExpression.fromText(expression.toText()));
  }

  @Test
  public void testEquals() {
    assertNotEquals(expression, this);
    assertFalse(expression.equals(null));
  }
}