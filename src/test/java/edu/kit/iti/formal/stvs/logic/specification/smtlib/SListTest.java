package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Created by csicar on 28.02.17.
 */
public class SListTest {
  private SList simple;

  private SList multivalue;
  private SList nested;
  @Before
  public void setupInstance() {
    this.simple = new SList("testValue");
    this.multivalue = new SList("val1", "val2", "val3");
    this.nested = new SList("val1", new SList("nested1.1", "nested1.2"), new SList("nested2.1"));
  }

  @Test
  public void isAtom() throws Exception {
    assertEquals(false, simple.isAtom());
    assertEquals(false, multivalue.isAtom());
    assertEquals(false, nested.isAtom());
  }

  @Test
  public void toText() throws Exception {
    assertEquals(" ( testValue ) ", simple.toText());
    assertEquals(" ( val1 val2 val3 ) ", multivalue.toText());
    assertEquals(" ( val1  ( nested1.1 nested1.2 )   ( nested2.1 )  ) ", nested.toText());
  }

  @Test
  public void addAllStringArguments() throws Exception {
    List<String> newElements = Arrays.asList("add1", "add2", "add3");

    simple.addAll("add1", "add2", "add3");
    assertEquals(
        new SList("testValue", "add1", "add2", "add3"),
        simple);
    multivalue.addAll("add1", "add2", "add3");
    assertEquals(
        new SList("val1", "val2", "val3", "add1", "add2", "add3"),
        multivalue);
    nested.addAll("add1", "add2", "add3");
    assertEquals(
        new SList("val1", new SList("nested1.1", "nested1.2"), new SList("nested2.1"), new SAtom
            ("add1"), new SAtom("add2"), new SAtom("add3")),
        nested
        );
  }

  @Test
  public void addAllArgumentExpressions() throws Exception {
    List<String> newElements = Arrays.asList("add1", "add2", "add3");

    simple.addAll(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3"));
    assertEquals(
        new SList("testValue", "add1", "add2", "add3"),
        simple);
    simple.addAll(
        new SAtom("add4"),
        new SAtom("add5")
    );
    assertEquals(
        new SList("testValue", "add1", "add2", "add3", "add4", "add5"),
        simple);


    multivalue.addAll(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3"));
    assertEquals(
        new SList("val1", "val2", "val3", "add1", "add2", "add3"),
        multivalue);

    nested.addAll(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3"));
    assertEquals(
        new SList("val1", new SList("nested1.1", "nested1.2"), new SList("nested2.1"), new SAtom
            ("add1"), new SAtom("add2"), new SAtom("add3")),
        nested
    );

    SList inner = new SList("inner1", "inner2");
    simple.addAll(inner);
    inner.addAll(new SAtom("inner3"));
    assertEquals(
        new SList("testValue", new SAtom("add1"), new SAtom("add2"), new SAtom("add3"),
            new SAtom("add4"), new SAtom("add5"), new SList
            ("inner1", "inner2", "inner3")),
        simple
    );
  }

  @Test
  public void addAllListOfExpressions() throws Exception {
    List<String> newElements = Arrays.asList("add1", "add2", "add3");

    simple.addAll(Arrays.asList(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3")));
    assertEquals(
        new SList("testValue", "add1", "add2", "add3"),
        simple);
    simple.addAll(Arrays.asList(
        new SAtom("add4"),
        new SAtom("add5")
    ));
    assertEquals(
        new SList("testValue", "add1", "add2", "add3", "add4", "add5"),
        simple);

    multivalue.addAll(Arrays.asList(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3")));
    assertEquals(
        new SList("val1", "val2", "val3", "add1", "add2", "add3"),
        multivalue);

    nested.addAll(Arrays.asList(
        new SAtom("add1"),
        new SAtom("add2"),
        new SAtom("add3")));
    assertEquals(
        new SList("val1", new SList("nested1.1", "nested1.2"), new SList("nested2.1"), new SAtom
            ("add1"), new SAtom("add2"), new SAtom("add3")),
        nested
    );

    SList inner = new SList("inner1", "inner2");
    simple.addAll(inner);
    inner.addAll(Arrays.asList(new SAtom("inner3")));
    assertEquals(
        new SList("testValue", new SAtom("add1"), new SAtom("add2"), new SAtom("add3"),
            new SAtom("add4"), new SAtom("add5"), new SList
            ("inner1", "inner2", "inner3")),
        simple
    );
  }

  @Test
  public void addListElements() throws Exception {

    simple.addListElements(Arrays.asList(
        "add1", "add2", "add3"));
    assertEquals(
        new SList("testValue", "add1", "add2", "add3"),
        simple);

    multivalue.addListElements(Arrays.asList(
        "add1", "add2", "add3"));
    assertEquals(
        new SList("val1", "val2", "val3", "add1", "add2", "add3"),
        multivalue);

    nested.addListElements(Arrays.asList(
        "add1", "add2", "add3"));
    assertEquals(
        new SList("val1", new SList("nested1.1", "nested1.2"), new SList("nested2.1"), new SAtom
            ("add1"), new SAtom("add2"), new SAtom("add3")),
        nested
    );
  }

  @Test
  public void getList() throws Exception {
    assertEquals(Arrays.asList(
        new SAtom("testValue")),
        simple.getList());
    assertEquals(Arrays.asList(
        new SAtom("val1"),
        new SAtom("val2"),
        new SAtom("val3")),
        multivalue.getList());
    assertEquals(Arrays.asList(
        new SAtom("val1"),
        new SList("nested1.1", "nested1.2"),
        new SList("nested2.1")),
        nested.getList());
  }

  @Test
  public void testEquals() throws Exception {
    assertEquals(new SList("testValue"), simple);
    assertEquals((SExpression) new SList("testValue"), simple);
    assertEquals(new SList("val1", "val2", "val3"), multivalue);
    assertEquals(new SList(Arrays.asList(
        new SAtom("val1"),
        new SList("nested1.1", "nested1.2"),
        new SList("nested2.1"))),
        nested
        );
    assertEquals(simple, simple);
    assertEquals(multivalue, multivalue);
    assertEquals(nested, nested);
    assertNotEquals(new SList("testValue", "val2"), simple);
    assertNotEquals(new SList(), simple);
    assertNotEquals(new SList("val1", "val2", "val3", "val4", "val4"), multivalue);
    assertNotEquals(new SList(), multivalue);
    assertNotEquals(this, simple);
    assertNotEquals(this, multivalue);
    assertNotEquals(this, nested);
    assertFalse(nested.equals(null));

  }

  @Test
  public void testHashCode() throws Exception {
    assertEquals(new SList("testValue").hashCode(), simple.hashCode());
    assertEquals(((SExpression) new SList("testValue")).hashCode(), simple.hashCode());
    assertEquals(new SList("val1", "val2", "val3").hashCode(), multivalue.hashCode());
    assertEquals(new SList(Arrays.asList(
        new SAtom("val1"),
        new SList("nested1.1", "nested1.2"),
        new SList("nested2.1"))).hashCode(),
        nested.hashCode()
    );
  }

  @Test
  public void toSexpr() throws Exception {
    Sexp sexp = SexpFactory.newNonAtomicSexp();
    sexp.add(SexpFactory.newAtomicSexp("testValue"));
    assertEquals(sexp, simple.toSexpr());
  }


  @Test
  public void testSexprConstructor() {
    Sexp sexp = SexpFactory.newNonAtomicSexp();
    sexp.add(SexpFactory.newAtomicSexp("testValue"));
    assertEquals(new SList(sexp), simple);
  }

  @Test
  public void toStringTest() throws Exception {
    assertNotEquals("", simple.toString());
  }

}