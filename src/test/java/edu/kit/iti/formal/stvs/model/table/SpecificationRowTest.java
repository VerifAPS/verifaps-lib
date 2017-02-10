package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.util.Callback;
import org.junit.Test;

import java.util.Collections;
import java.util.HashMap;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationRowTest {

  private static <E extends Observable> Callback<E, Observable[]> identityExtractor() {
    return param -> new Observable[] { param };
  }

  private final StringProperty toBeChanged = new SimpleStringProperty("");
  private final SpecificationRow<StringProperty> specRow =
      new SpecificationRow<>(new HashMap<>(), identityExtractor());

  public SpecificationRowTest() {
    specRow.getCells().put("abc", toBeChanged);
  }

  private int listenerCalls = 0;

  @Test
  public void testInvalidationListener() {
    specRow.addListener(observable -> listenerCalls++);

    assertEquals("listener calls before change", 0, listenerCalls);
    toBeChanged.set("XYZ");
    assertEquals("listener calls after change", 1, listenerCalls);
  }

  @Test
  public void testNestedRows() {
    ObservableList<SpecificationRow<StringProperty>> rows =
        FXCollections.observableList(
            Collections.singletonList(specRow),
            identityExtractor()
        );
    rows.addListener((Observable obs) -> listenerCalls++);

    assertEquals("listener calls before change", 0, listenerCalls);
    toBeChanged.set("XXX");
    assertEquals("listener calls after change", 1, listenerCalls);

    StringProperty toBeAddedChangedRemoved = new SimpleStringProperty("");

    rows.get(0).getCells().put("toBeAddedChangedRemoved", toBeAddedChangedRemoved);
    assertEquals("listener calls after adding", 2, listenerCalls);

    toBeAddedChangedRemoved.set("ASDF");
    assertEquals("listener calls after changing added", 3, listenerCalls);

    rows.get(0).getCells().remove("toBeAddedChangedRemoved");
    assertEquals("listener calls after removing", 4, listenerCalls);

    toBeAddedChangedRemoved.set("SHOULD NOT FIRE EVENT");
    assertEquals("listener calls after changing cell that was removed", 4, listenerCalls);
  }
}
