package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * Created by bal on 25.02.17.
 */
public class HybridCellTest {
  private HybridCell<ConstraintCell> hybridCell;

  @Before
  public void setUp() throws Exception {
    hybridCell = new HybridCell<>("A", new ConstraintCell("3"));
  }

  @Test
  public void setFromString() throws Exception {
    assertNotEquals("asdf", hybridCell.getAsString());
    hybridCell.setFromString("asdf");
    assertEquals("asdf", hybridCell.getAsString());
  }

  @Test
  public void testSetComment() {
    assertNotEquals("asdf", hybridCell.getAsString());
    hybridCell.setComment("I am a comment!");
    assertEquals("I am a comment!", hybridCell.getComment());
  }

}