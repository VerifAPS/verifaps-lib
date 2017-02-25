package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by bal on 25.02.17.
 */
public class ConstraintDurationTest {
  private ConstraintDuration duration;

  @Before
  public void setUp() {
    duration = new ConstraintDuration("[2,3]");
    duration.setComment("I am a comment!");
  }

  @Test
  public void testCopyConstructor() {
    ConstraintDuration clone = new ConstraintDuration(duration);
    assertNotSame(clone, duration);
    assertEquals(clone, duration);
  }

  @Test
  public void setFromString() {
    duration.setFromString("[4,-]");
    assertEquals("[4,-]", duration.getAsString());
  }

  @Test
  public void equals() {
    ConstraintDuration identical = new ConstraintDuration("[2,3]");
    identical.setComment("I am a comment!");
    assertEquals(identical, duration);
    assertNotEquals(duration, null);
    identical.setFromString("[4,-]");
    assertNotEquals(identical, duration);
  }

}