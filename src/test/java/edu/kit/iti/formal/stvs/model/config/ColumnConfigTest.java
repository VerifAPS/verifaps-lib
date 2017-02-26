package edu.kit.iti.formal.stvs.model.config;

import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by bal on 26.02.17.
 */
public class ColumnConfigTest {

  private ColumnConfig config;

  @Before
  public void setUp() {
    config = new ColumnConfig(130);
  }

  @Test
  public void testGetSetColwidth() {
    // default colwidth
    assertEquals(100, new ColumnConfig().getWidth(), TestUtils.EPSILON);
    assertEquals(130, config.getWidth(), TestUtils.EPSILON);
    config.setWidth(120);
    assertEquals(120, config.getWidth(), TestUtils.EPSILON);
  }

  @Test(expected=IllegalArgumentException.class)
  public void testIllegalColwidthConstructor() {
    config = new ColumnConfig(0);
  }

  @Test(expected=IllegalArgumentException.class)
  public void testSetIllegalWidth() {
    config.setWidth(-1);
  }

  @Test
  public void testEquals() throws Exception {
    ColumnConfig identical = new ColumnConfig(130);
    assertEquals(identical, config);
    assertNotEquals(null, config);
    assertEquals(config, config);
    identical.setWidth(100);
    assertNotEquals(identical, config);
  }

  @Test
  public void testHashCode() throws Exception {
    ColumnConfig identical = new ColumnConfig(130);
    assertEquals(identical.hashCode(), config.hashCode());
    assertEquals(config.hashCode(), config.hashCode());
    identical.setWidth(100);
    assertNotEquals(identical.hashCode(), config.hashCode());
  }

}