package edu.kit.iti.formal.stvs.model.common;

import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by Lukas on 22.02.2017.
 *
 * @author Lukas
 */
public class CodeIoVariableTest {
  private CodeIoVariable var1 = new CodeIoVariable(VariableCategory.INPUT, "BOOL", "var");
  private CodeIoVariable var2 = new CodeIoVariable(VariableCategory.INPUT, "BOOL", "var");
  private Object object = new Object();

  @Test
  public void equalsCodeIoVariable() throws Exception {
    assertTrue(var1.equals(var2));
    assertNotEquals(new CodeIoVariable(VariableCategory.INPUT, "INT", "var"), var2);
  }

  @Test
  public void testHashCode() {
    assertEquals(var1.hashCode(), var2.hashCode());
    assertNotEquals(new CodeIoVariable(VariableCategory.INPUT, "INT", "var").hashCode(),
        var2.hashCode());
  }

  @Test
  public void equalsObject() throws Exception {
    assertTrue(!var1.equals(object));

  }

}