package edu.kit.iti.formal.stvs.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * Created by leonk on 08.02.2017.
 */
public class ProcessOutputAsyncTask extends AsyncTask<Optional<String>> {
  public ProcessOutputAsyncTask(Process process, Consumer<Optional<String>> runOnPlatform) {
    super(createProcessHandler(process), runOnPlatform);
  }

  private static Supplier<Optional<String>> createProcessHandler(Process process) {
    //The new line chars are all transformed into a single \n
    return () -> {
      String result = "";
      final BufferedReader reader = new BufferedReader(
          new InputStreamReader(process.getInputStream()));
      String line;
      try {
        while ((line = reader.readLine()) != null) {
          result += line+"\n";
        }
        return Optional.of(result);
      } catch (IOException e) {
        e.printStackTrace();
        return Optional.empty();
      }
    };
  }
}
