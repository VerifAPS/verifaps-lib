package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 17.01.2017.
 */
public class OptionalPropertyBaseTest {
  @Test
  public void testClear() {
    StringProperty testProperty = new SimpleStringProperty("Das ist ein Test");
    OptionalPropertyBase<String, StringProperty> testOptional = new OptionalPropertyBase<>(testProperty);
    assertFalse(testOptional.isNull().get());
    testOptional.clear();
    assertTrue(testOptional.isNull().get());
    //Removing the optionals value does not affect the wrapped property.
    assertEquals("Das ist ein Test", testOptional.getProperty().get());
    testOptional.set(null);
    assertEquals("Das ist ein Test", testOptional.getProperty().get());
  }

  @Test
  public void testListen() {
    BooleanProperty booleanProperty = new SimpleBooleanProperty(false);
    IntegerProperty testProperty = new SimpleIntegerProperty(4);
    OptionalPropertyBase<Number, IntegerProperty> testOptional = new OptionalPropertyBase<>(testProperty);
    testOptional.isNull().addListener(change -> booleanProperty.setValue(true));
    testOptional.clear();
    assertTrue(booleanProperty.get());
  }

  @Test
  public void testAdditional() {
    IntegerProperty testProperty = new SimpleIntegerProperty(4);
    OptionalPropertyBase<Number, IntegerProperty> testOptional =
            new OptionalPropertyBase<>(testProperty);
    testOptional.set(5);
    assertEquals(5, testOptional.getValue());
    testOptional.setValue(4);
    assertEquals(4, testOptional.getValue());
  }
}