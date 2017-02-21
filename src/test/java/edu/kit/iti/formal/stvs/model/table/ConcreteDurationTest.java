package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 */
public class ConcreteDurationTest {

  private ConcreteDuration durationA;

  @Before
  public void setUp() {
    durationA = new ConcreteDuration(1, 2);
  }

  @Test
  public void testGetDuration() {
    assertEquals(2, durationA.getDuration());
  }

  @Test
  public void testGetBeginCycle() {
    assertEquals(1, durationA.getBeginCycle());
  }

  @Test
  public void testToString() {
    assertEquals("2", durationA.toString());
  }

  @Test
  public void testGetEndCycle() {
    ConcreteDuration duration = new ConcreteDuration(3, 4);
    assertEquals(7, duration.getEndCycle());
    duration = new ConcreteDuration(0,0);
    assertEquals(0, duration.getEndCycle());
    duration = new ConcreteDuration(1, 0);
    assertEquals(1, duration.getEndCycle());
  }

  @Test(expected = IllegalArgumentException.class)
  public void testConstructorInvalidBeginCycle() {
    ConcreteDuration duration = new ConcreteDuration(-1, 1);
  }

  @Test(expected = IllegalArgumentException.class)
  public void testConstructorInvalidDuration() {
    ConcreteDuration duration = new ConcreteDuration(1, -1);
  }

  @Test
  public void testEquals() {
    ConcreteDuration durationB = new ConcreteDuration(1, 2);
    assertEquals(durationA, durationB);
    ConcreteDuration durationC = new ConcreteDuration(1, 3);
    assertNotEquals(durationA, durationC);
    ConcreteDuration durationD = new ConcreteDuration(2, 2);
    assertNotEquals(durationA, durationD);
    ConstraintDuration durationE = new ConstraintDuration("2");
    assertNotEquals(durationA, durationE);
    assertNotEquals(durationA, null);
  }
}
