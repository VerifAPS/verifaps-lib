package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
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
  public void addGlobalConstrainsAsArguments() throws Exception {
    simple.addGlobalConstrains(new SAtom("new"), new SAtom("new2"));
    assertEquals(fromString(
        "a bb ccc",
        "d ee fff new new2"
    ), simple);
    other.addGlobalConstrains(new SList("newA", new SList("newB", "newC")));
    assertEquals(fromString(
        "l o s",
        "ggg (1 2 3 h) i (newA (newB newC))"
    ), other);
  }

  @Test
  public void addGlobalConstrainsAsList() throws Exception {
    simple.addGlobalConstrains(Arrays.asList(new SAtom("new"), new SAtom("new2")));
    assertEquals(fromString(
        "a bb ccc",
        "d ee fff new new2"
    ), simple);
    other.addGlobalConstrains(Arrays.asList(new SList("newA", new SList("newB", "newC"))));
    assertEquals(fromString(
        "l o s",
        "ggg (1 2 3 h) i (newA (newB newC))"
    ), other);
  }

  @Test
  public void addHeaderDefinitionsAsArguments() throws Exception {
    simple.addHeaderDefinitions(new SAtom("new"), new SAtom("new2"));
    assertEquals(fromString(
        "a bb ccc new new2",
        "d ee fff"
    ), simple);
    other.addHeaderDefinitions(new SList("newA", new SList("newB", "newC")));
    assertEquals(fromString(
        "l o s (newA (newB newC))",
        "ggg (1 2 3 h) i"
    ), other);
  }

  @Test
  public void addHeaderDefinitionsAsList() throws Exception {
    simple.addHeaderDefinitions(Arrays.asList(new SAtom("new"), new SAtom("new2")));
    assertEquals(fromString(
        "a bb ccc new new2",
        "d ee fff"
    ), simple);
    other.addHeaderDefinitions(Arrays.asList(new SList("newA", new SList("newB", "newC"))));
    assertEquals(fromString(
        "l o s (newA (newB newC))",
        "ggg (1 2 3 h) i"
    ), other);
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
    assertEquals(Arrays.asList(
        new SAtom("a"),
        new SAtom("bb"),
        new SAtom("ccc")
    ), simple.getVariableDefinitions());
  }

  @Test
  public void testToString() throws Exception {
    assertFalse(simple.toString().isEmpty());
  }

  @Test
  public void equals() throws Exception {
    SmtModel simpleCompare = fromString(
        "a bb ccc",
        "d ee fff"
    );
    SmtModel otherCompare = fromString(
        "l o s",
        "ggg (1 2 3 h) i"
    );
    assertEquals(simpleCompare, simple);
    assertEquals(otherCompare, other);
    assertNotEquals(this, simple);
    assertNotEquals(this, other);
    assertNotEquals(simple, other);
    assertNotEquals("", other);
    assertFalse(simple.equals(null));
    assertEquals(simple, simple);
  }

  @Test
  public void testHashCode() throws Exception {
    SmtModel simpleCompare = fromString(
        "a bb ccc",
        "d ee fff"
    );
    SmtModel otherCompare = fromString(
        "l o s",
        "ggg (1 2 3 h) i"
    );
    assertEquals(simpleCompare.hashCode(), simple.hashCode());
    assertEquals(otherCompare.hashCode(), other.hashCode());
  }


  @Test
  public void testEmptyConstructor() {
    SmtModel model = new SmtModel();
    assertEquals(new ArrayList<>(), model.getVariableDefinitions());
    assertEquals(new ArrayList<>(), model.getGlobalConstraints());
  }
}