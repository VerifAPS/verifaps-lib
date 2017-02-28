package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by bal on 25.02.17.
 */
public class ConstraintCellTest {
  private ConstraintCell constraintCell;

  @Before
  public void setUp() {
    constraintCell = new ConstraintCell("Test");
    constraintCell.setComment("I am a comment!");
  }

  @Test
  public void testCopyConstructor() {
    ConstraintCell clone = new ConstraintCell(constraintCell);
    assertNotSame(constraintCell, clone);
    assertEquals(constraintCell, clone);
  }

  @Test
  public void testEquals() {
    ConstraintCell identical = new ConstraintCell("Test");
    identical.setComment("I am a comment!");
    assertEquals(constraintCell, identical);
    assertNotEquals(constraintCell, null);
    assertNotEquals(constraintCell, new ConstraintCell("Test"));
  }

  @Test
  public void testToString() {
    assertEquals("Test (comment: \"I am a comment!\")", constraintCell.toString());
  }

  @Test
  public void testSetFromString() {
    constraintCell.setFromString("Some string");
    assertEquals("Some string", constraintCell.getAsString());
  }
}