package edu.kit.iti.formal.stvs.logic.io;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Created by csicar on 20.07.17.
 */
public class ExecutableLocator {
  public static Optional<File> findExecutableFile(String executableName) {
    String envPath = System.getenv("PATH");
    if (envPath.isEmpty()) {
      return Optional.empty();
    }
    Optional<File> path = Arrays.stream(envPath.split(":")).map(File::new)
        .filter(File::exists)
        .filter(file -> {
      if (!file.isDirectory()) {
        return false;
      } else {
        File[] files = file.listFiles((file1, s) -> s.equals(executableName));
        if (files == null) {
          return false;
        }
        return files.length != 0;
      }
    }).findAny();
    return path.map(file -> new File(file, executableName));
  }

  public static Optional<String> findExecutableFileAsString(String executableName) {
    return findExecutableFile(executableName).map(File::toString);
  }
}
