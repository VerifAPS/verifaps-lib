package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.StvsApplication;

import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class TestUtils {

  public enum FileType {
    SESSION, CONCRETE, CONSTRAINT, CONFIG
  }

  private static final Map<FileType, String> prefixes;
  static {
    prefixes = new HashMap<>();
    prefixes.put(FileType.SESSION, "session");
    prefixes.put(FileType.CONCRETE, "concrete_spec");
    prefixes.put(FileType.CONSTRAINT, "constraint_spec");
    prefixes.put(FileType.CONFIG, "config");
  }

  public static String removeWhitespace(String input) {
    return input.replaceAll("\\s+", "");
  }

  public static List<File> getTestFiles(FileType type) throws URISyntaxException {
    List<File> res = new ArrayList<>();
    for (File testSet : getTestSets()) {
      String[] children = testSet.list();
      if (children != null) {
        for (String childName : children) {
          if (childName.startsWith(prefixes.get(type))) {
            res.add(new File(testSet.getAbsolutePath() + File.separator + childName));
          }
        }
      }
    }
    return res;
  }

  private static List<File> getTestSets() throws URISyntaxException {
    File testSetsDirectory = new File(StvsApplication.class
        .getResource("testSets").toURI());
    List<File> res = new ArrayList<>();
    for (String childName : testSetsDirectory.list()) {
      res.add(new File(testSetsDirectory.getAbsolutePath() + File.separator + childName));
    }
    return res;
  }

  public static void main(String[] args) throws URISyntaxException {
    for (FileType type : FileType.values()) {
      for (File file : getTestFiles(type)) {
        System.out.println(file.getName());
      }
    }
  }
}
