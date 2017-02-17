package edu.kit.iti.formal.stvs.model.config;

import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import static org.junit.Assert.assertEquals;

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
    for (int i = 0; i < history.HISTORY_DEPTH * 2; i++) {
      history.addFilename("filePath" + i);
    }
    assertEquals(history.getFilenames().size(), history.HISTORY_DEPTH);
  }

  @Test
  public void testCopyConstructor() {
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

  @Test(expected=IllegalArgumentException.class)
  public void testCopyConstructorException() {
    ArrayList<String> codePaths = new ArrayList<String>();
    for (int i = 0; i < history.HISTORY_DEPTH * 2; i++) {
      codePaths.add("SomeCode" + i);
    }
    history = new History(codePaths);
  }

  @Test
  public void testAddSFilename() {
    history.addFilename("someSpec");
    assertEquals(history.getFilenames().get(0), "someSpec");
  }
}
