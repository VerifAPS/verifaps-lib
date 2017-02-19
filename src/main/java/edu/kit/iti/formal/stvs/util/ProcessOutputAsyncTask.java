package edu.kit.iti.formal.stvs.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Created by leonk on 08.02.2017.
 * @author Leon Kaucher
 */
public class ProcessOutputAsyncTask extends AsyncTask<Optional<String>> {
  public ProcessOutputAsyncTask(ProcessBuilder processBuilder, String input, Consumer<Optional<String>> runLater) {
    super(createProcessHandler(processBuilder, input), runLater);
  }

  private static Function<AtomicBoolean, Optional<String>> createProcessHandler(ProcessBuilder processBuilder, String input) {
    //The new line chars are all transformed into a single \n
    return (isRunning) -> {
      String result = "";
      try {
        Process process = processBuilder.start();
        PrintStream printStream = new PrintStream(process.getOutputStream());
        printStream.print(input);
        printStream.close();
        final BufferedReader reader = new BufferedReader(
            new InputStreamReader(process.getInputStream()));
        String line;
        while ((line = reader.readLine()) != null && isRunning.get()) {
          result += line + "\n";
        }
        if (isRunning.get()) {
          return Optional.of(result);
        } else {
          return Optional.empty();
        }
      } catch (IOException e) {
        throw new RuntimeException(e);
      }
    };
  }
}
