package edu.kit.iti.formal.stvs.model.config;

import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 * @author Benjamin Alt
 */
public class HistoryTest {
  private History history;

  @Before
  public void setUp() {
    history = new History();
  }

  @Test
  public void testBufferSize() {
    assertEquals(0, history.getFilenames().size());
    for (int i = 0; i < History.HISTORY_DEPTH * 2; i++) {
      history.addFilename("filePath" + i);
    }
    assertEquals(History.HISTORY_DEPTH, history.getFilenames().size());
  }

  @Test
  public void testConstructor() {
    ArrayList<String> filePaths = new ArrayList<String>();
    filePaths.add("CodeOne");
    filePaths.add("CodeTwo");
    filePaths.add("SpecOne");
    history = new History(filePaths);
    List<String> filePathsAfter = history.getFilenames();
    assertEquals(filePathsAfter.get(0), "CodeOne");
    assertEquals(filePathsAfter.get(1), "CodeTwo");
    assertEquals(filePathsAfter.get(2), "SpecOne");
  }

  @Test(expected = IllegalArgumentException.class)
  public void testConstructorException() {
    ArrayList<String> codePaths = new ArrayList<String>();
    for (int i = 0; i < History.HISTORY_DEPTH * 2; i++) {
      codePaths.add("SomeCode" + i);
    }
    history = new History(codePaths);
  }

  @Test
  public void testAddSpecFilename() {
    history.addFilename("someSpec");
    assertEquals(history.getFilenames().get(0), "someSpec");
  }

  @Test
  public void testSetAll() {
    testConstructor();
    History clone = new History();
    clone.setAll(history);
    assertEquals(history, clone);
  }

  @Test
  public void testEquals() {
    testConstructor();
    ArrayList<String> filePaths = new ArrayList<String>();
    filePaths.add("CodeOne");
    filePaths.add("CodeTwo");
    filePaths.add("SpecOne");
    History identical = new History(filePaths);
    assertEquals(history, identical);
    assertNotEquals(null, history);
    assertEquals(history, history);
    identical.getFilenames().add("Another filename!");
    assertNotEquals(history, identical);
  }

  @Test
  public void testHashCode() {
    testConstructor();
    ArrayList<String> filePaths = new ArrayList<String>();
    filePaths.add("CodeOne");
    filePaths.add("CodeTwo");
    filePaths.add("SpecOne");
    History identical = new History(filePaths);
    assertEquals(history.hashCode(), identical.hashCode());
    assertEquals(history.hashCode(), history.hashCode());
    identical.getFilenames().add("Another filename!");
    assertNotEquals(history.hashCode(), identical.hashCode());
  }
}
