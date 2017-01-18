package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 18.01.2017.
 */
public class FreeVariableTest {
  @Test
  public void testCreation() throws IllegalValueTypeException {
    FreeVariable testVar1 = new FreeVariable("testVar1", TypeBool.BOOL);
    FreeVariable testVar2 = new FreeVariable("testVar2", TypeInt.INT, new ValueInt(1233));
    assertTrue(testVar1.getType().checksAgainst(TypeBool.BOOL));
    assertEquals(testVar1.getName(), "testVar1");
    assertEquals(testVar1.getDefaultValue(), TypeBool.BOOL.generateDefaultValue());
    assertEquals(testVar2.getDefaultValue(), new ValueInt(1233));
  }

  @Test
  public void testAutoErrorHandling() throws IllegalValueTypeException {
    //Tests if the value is set to types default value in case of type mismatch
    FreeVariable var = new FreeVariable("testVar2", TypeInt.INT, new ValueInt(1233));
    var.setType(TypeBool.BOOL);
    assertEquals(var.getType(), TypeBool.BOOL);
    assertEquals(var.getDefaultValue(), TypeBool.BOOL.generateDefaultValue());
  }

  @Test
  public void testWrongValueType() throws IllegalValueTypeException {
    //Test if an exception is thrown if default value is set to a value of wrong type
    FreeVariable var = new FreeVariable("testVar2", TypeInt.INT, new ValueInt(1233));
    try {
      var.setDefaultValue(ValueBool.FALSE);
    } catch (IllegalValueTypeException e) {
      assertEquals(e.getExpectedType(), TypeInt.INT);
      assertEquals(e.getMistypedValue().getType(), TypeBool.BOOL);
    }
  }

  @Test
  public void testProperties() {
    //Test if the defaultValueProperty listener is called if the value is
    // set to types default value in case of type mismatch
    BooleanProperty gotCalled = new SimpleBooleanProperty(false);
    FreeVariable var = new FreeVariable("test1", TypeBool.BOOL);
    var.defaultValueProperty().addListener(value -> gotCalled.set(true));
    var.setType(TypeInt.INT);
    assertTrue(gotCalled.get());
    assertEquals(var.getDefaultValue(), TypeInt.INT.generateDefaultValue());
  }
}
