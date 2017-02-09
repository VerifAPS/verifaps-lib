package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;

import java.io.IOException;
import java.io.PrintStream;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3Solver {
  //TODO: Better way to call z3 than forcing it to be in PATH
  private static String z3PATH = "z3";

  public static void concretize(String smtString, Consumer<Optional<String>> resultConsumer) throws IOException {
    Process process = new ProcessBuilder(z3PATH, "-in").start();
    PrintStream printStream = new PrintStream(process.getOutputStream());
    printStream.print(smtString);
    printStream.close();
    new ProcessOutputAsyncTask(process, resultConsumer).start();
  }
}
