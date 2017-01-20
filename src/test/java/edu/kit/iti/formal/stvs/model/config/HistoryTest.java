package edu.kit.iti.formal.stvs.model.config;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Created by bal on 21.01.17.
 */
public class HistoryTest {
  private History history;

  @Before
  public void setUp() {
    history = new History();
  }

  @Test
  public void testBufferSize() {
    assertEquals(0, history.getCodeFiles().size());
    assertEquals(0, history.getSpecFiles().size());
    for (int i = 0; i < history.HISTORY_DEPTH * 2; i++) {
      history.addCodeFile("codePath" + i);
      history.addSpecFile("specPath" + i);
    }
    assertEquals(history.getCodeFiles().size(), history.HISTORY_DEPTH);
    assertEquals(history.getSpecFiles().size(), history.HISTORY_DEPTH);
  }

  @Test
  public void testCopyConstructor() {
    ArrayList<String> codePaths = new ArrayList<String>();
    codePaths.add("CodeOne");
    codePaths.add("CodeTwo");
    HashSet<String> specPaths = new HashSet<String>();
    specPaths.add("SpecOne");
    history = new History(codePaths, specPaths);
    List<String> codePathsAfter = history.getCodeFiles();
    List<String> specPathsAfter = history.getSpecFiles();
    assertEquals(codePathsAfter.get(0), "CodeOne");
    assertEquals(codePathsAfter.get(1), "CodeTwo");
    assertEquals(specPathsAfter.get(0), "SpecOne");
  }

  @Test(expected=IllegalArgumentException.class)
  public void testCopyConstructorException() {
    ArrayList<String> codePaths = new ArrayList<String>();
    for (int i = 0; i < history.HISTORY_DEPTH * 2; i++) {
      codePaths.add("SomeCode" + i);
    }
    HashSet<String> specPaths = new HashSet<String>();
    specPaths.add("SpecOne");
    history = new History(codePaths, specPaths);
  }

  @Test
  public void testAddSpec() {
    history.addSpecFile("someSpec");
    assertEquals(history.getSpecFiles().get(0), "someSpec");
  }

  @Test
  public void testAddCode() {
    history.addCodeFile("someCode");
    assertEquals(history.getCodeFiles().get(0), "someCode");
  }
}
