package edu.kit.iti.formal.stvs.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Optional;

/**
 * Created by leonk on 08.02.2017.
 */
public class ProcessOutputHandler {
  public static Optional<String> handle(Process process) {
    //The new line chars are all transformed into a single \n
    String result = "";
    final BufferedReader reader = new BufferedReader(
        new InputStreamReader(process.getInputStream()));
    String line;
    try {
      while ((line = reader.readLine()) != null) {
        result += line + "\n";
      }
      return Optional.of(result);
    } catch (IOException e) {
      e.printStackTrace();
      return Optional.empty();
    }
  }
}
