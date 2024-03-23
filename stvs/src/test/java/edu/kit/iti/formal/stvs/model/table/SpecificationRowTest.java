package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.util.Callback;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationRowTest {

  private static <E extends Observable> Callback<E, Observable[]> identityExtractor() {
    return param -> new Observable[] {param};
  }

  private final StringProperty toBeChanged = new SimpleStringProperty("");
  private SpecificationRow<StringProperty> specRow;
  private int listenerCalls;

  @Before
  public void setUp() {
    specRow = new SpecificationRow<>(new HashMap<>(), identityExtractor());
    specRow.getCells().put("abc", toBeChanged);
    listenerCalls = 0;
  }

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

  @Test
  public void testUnobservableRow() {
    Map<String, StringProperty> cells = new HashMap<>();
    cells.put("abc", toBeChanged);
    SpecificationRow unobservable = SpecificationRow.createUnobservableRow(cells);
    unobservable.addListener(observable -> listenerCalls++);
    assertEquals("listener calls before change", 0, listenerCalls);
    toBeChanged.set("XYZ");
    assertEquals("listener calls after change", 0, listenerCalls);
    cells.put("def", new SimpleStringProperty("test"));
    assertEquals("listener calls after add", 0, listenerCalls);
  }

  @Test
  public void testEquals() {
    SpecificationRow otherRow = new SpecificationRow<>(new HashMap<>(), identityExtractor());
    otherRow.getCells().put("abc", toBeChanged);
    assertEquals(otherRow, specRow);
    assertEquals(specRow, specRow);
    otherRow.getCells().put("abc", new SimpleStringProperty("something else"));
    assertNotEquals(otherRow, specRow);
    assertNotEquals(specRow, null);
  }

  @Test
  public void testHashCode() {
    SpecificationRow otherRow = new SpecificationRow<>(new HashMap<>(), identityExtractor());
    otherRow.getCells().put("abc", toBeChanged);
    assertEquals(otherRow.hashCode(), specRow.hashCode());
    otherRow.getCells().put("abd", new SimpleStringProperty("something else"));
    assertNotEquals(otherRow.hashCode(), specRow.hashCode());
  }
}
