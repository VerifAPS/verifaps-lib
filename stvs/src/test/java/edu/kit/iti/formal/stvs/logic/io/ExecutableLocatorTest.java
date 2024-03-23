package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.TestUtils;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;
import java.util.Optional;

import static org.junit.Assert.*;

/**
 * Created by csicar on 20.07.17.
 */
public class ExecutableLocatorTest {


  @Test
  public void testPathWithZ3Linux() throws Exception {
    TestUtils.assumeZ3Exists();

    Optional<File> z3 = ExecutableLocator.findExecutableFile("z3");
    assertEquals(Optional.of(new File("/usr/bin/z3")), z3);
    System.out.println(z3.toString());
  }

  @Test
  public void testPathWithZ3LinuxString() throws Exception {
    TestUtils.assumeNuXmvExists();

    Optional<File> nuXmv = ExecutableLocator.findExecutableFile("nuXmv");
    assertEquals(Optional.of(new File("/usr/local/bin/nuXmv")), nuXmv);
    System.out.println(nuXmv.toString());
  }

  @Test
  public void name() throws Exception {
    Optional<File> empty = ExecutableLocator.findExecutableFile("other");
    assertEquals(Optional.empty(), empty);
  }
}