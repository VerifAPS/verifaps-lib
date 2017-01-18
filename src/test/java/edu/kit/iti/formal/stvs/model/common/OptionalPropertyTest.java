package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by leonk on 17.01.2017.
 */
public class OptionalPropertyTest {
  @Test
  public void testMain(){
    OptionalProperty<String> test = new OptionalProperty<>(new SimpleStringProperty("TEST"));
    assertTrue(test.isNotNull().get());
    test.clear();
    assertTrue(test.isNull().get());
  }
}