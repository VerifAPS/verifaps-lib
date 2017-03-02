package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.regex.Pattern;

import static org.junit.Assert.*;

/**
 * Created by csicar on 02.03.17.
 */
public class SmtModelTest {
  private SmtModel simple;
  private SmtModel other;

  private SmtModel fromString(String vars, String constr) {
    return new SmtModel(
        ((SList) SExpression.fromText("("+constr+")")).getList(),
        ((SList) SExpression.fromText("("+vars+")")).getList());
  }

  private void assertMatches(String pattern, String string) {
    String escapedPattern = "\\s?"+pattern
        .replace(" ", "\\s+")
        .replace("(", "\\(")
                .replace(")", "\\)")+"\\s?";
    assertTrue("Tried to match <<"+string+">> with "+escapedPattern,
        Pattern.matches(escapedPattern, string));
  }

  @Before
  public void setup() {
    this.simple = fromString(
        "a bb ccc",
        "d ee fff"
    );
    this.other = fromString(
        "l o s",
        "ggg (1 2 3 h) i"
        );
  }

  @Test
  public void combine() throws Exception {
    simple.combine(other);
    assertEquals(fromString(
      "a bb ccc l o s",
        "d ee fff ggg (1 2 3 h) i"
    ),
        simple);
  }

  @Test
  public void isAtom() throws Exception {
    assertFalse(simple.isAtom());
  }

  @Test
  public void toSexpr() throws Exception {
    assertEquals(
        SExpression.fromText("(a bb ccc ( assert d ) ( assert ee ) ( assert fff) )"),
        SExpression.fromSexp(simple.toSexpr())
    );
  }

  @Test
  public void headerToText() throws Exception {
    String result = simple.headerToText();
    assertMatches("a bb ccc", result);

    String result2 = other.headerToText();
    System.out.println(result2);
    assertMatches("l o s", result2);
  }

  @Test
  public void globalConstraintsToText() throws Exception {
    String pattern = "( assert d ) ( assert ee ) ( assert fff )";
    assertMatches(pattern, simple.globalConstraintsToText());

    assertMatches("( assert ggg ) ( assert ( 1 2 3 h ) ) ( assert i )",
        other.globalConstraintsToText());
  }

  @Test
  public void toText() throws Exception {
    assertMatches("a bb ccc ( assert d ) ( assert ee ) ( assert fff )", simple.toText());
    assertMatches("l o s ( assert ggg ) ( assert ( 1 2 3 h ) ) ( assert i )", other.toText());
  }

  @Test
  public void addGlobalConstrains() throws Exception {

  }

  @Test
  public void addGlobalConstrains1() throws Exception {

  }

  @Test
  public void addHeaderDefinitions() throws Exception {

  }

  @Test
  public void addHeaderDefinitions1() throws Exception {

  }

  @Test
  public void getGlobalConstraints() throws Exception {
    assertEquals(Arrays.asList(
        new SAtom("d"),
        new SAtom("ee"),
        new SAtom("fff")
    ), simple.getGlobalConstraints());
  }

  @Test
  public void getVariableDefinitions() throws Exception {

  }

  @Test
  public void testToString() throws Exception {

  }

  @Test
  public void equals() throws Exception {

  }

  @Test
  public void testHashCode() throws Exception {

  }

}