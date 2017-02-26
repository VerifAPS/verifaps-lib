package edu.kit.iti.formal.stvs.model.table;

import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.*;

/**
 * Created by bal on 26.02.17.
 */
public class SpecificationColumnTest {
  private SpecificationColumn<Integer> column;

  @Before
  public void setUp() {
    column = new SpecificationColumn<>(Arrays.asList(1,2,3,4,5));
  }

  @Test
  public void testEquals() throws Exception {
    SpecificationColumn identical = new SpecificationColumn<>(Arrays.asList(1,2,3,4,5));
    assertEquals(identical, column);
    column.setComment("Comment");
    assertNotEquals(identical, column);
    identical.setComment("Comment");
    assertEquals(identical, column);
    identical.setComment("Different comment");
    assertNotEquals(identical, column);
    assertNotEquals(null, column);
    assertEquals(column, column);
  }

  @Test
  public void testGetSetComment() {
    assertEquals("", column.getComment());
    column.setComment("Comment");
    assertEquals("Comment", column.getComment());
    column.setComment("NewComment");
    assertEquals("NewComment", column.getComment());
  }

  @Test
  public void testToString() throws Exception {
    column.setComment("Comment");
    assertEquals("SpecificationColumn(cells: [1, 2, 3, 4, 5], comment: Comment)",
        column.toString());
  }
}