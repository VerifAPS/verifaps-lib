package edu.kit.iti.formal.stvs.logic.io.xml;

import java.io.File;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 * @author Benjamin Alt
 */
public class TestUtils {
  public static String removeWhitespace(String input) {
    return input.replaceAll("\\s+", "");
  }
}
