package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Created by leonk on 19.01.2017.
 */
public class ProxyBindingTest {
  @Test
  public void mainTest(){
    TestObservable testObservable = new TestObservable();
    ProxyBinding<TestObservable> proxy = new ProxyBinding<>(
            testObservable,
            testObservable.stringProperty,
            testObservable.booleanProperty
        );
    IntegerProperty countCalls = new SimpleIntegerProperty(0);
    InvalidationListener invaldationListener =
        (i -> countCalls.setValue(countCalls.get()+1));
    proxy.addListener(invaldationListener);
    testObservable.booleanProperty.setValue(true);
    testObservable.stringProperty.setValue("TEST");
    assertEquals(2, countCalls.get());
    proxy.removeListener(invaldationListener);
    testObservable.booleanProperty.setValue(false);
    testObservable.stringProperty.setValue("TEST2");
    assertEquals(2, countCalls.get());
  }
}

class TestObservable{
  public StringProperty stringProperty = new SimpleStringProperty();
  public BooleanProperty booleanProperty = new SimpleBooleanProperty();
}