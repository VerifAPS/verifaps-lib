package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import org.junit.Before;
import org.junit.Test;

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
  }

  @Test
  public void isAtom() throws Exception {
    assertEquals(false, simple.isAtom());
  }

  @Test
  public void toText() throws Exception {
    assertEquals(" ( testValue ) ", simple.toText());
  }

  @Test
  public void addAll() throws Exception {

  }

  @Test
  public void addAll1() throws Exception {

  }

  @Test
  public void addAll2() throws Exception {

  }

  @Test
  public void addListElements() throws Exception {

  }

  @Test
  public void getList() throws Exception {

  }

  @Test
  public void testEquals() throws Exception {

  }

  @Test
  public void testHashCode() throws Exception {

  }

}