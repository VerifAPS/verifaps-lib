package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.util.AsyncTask;
import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import org.junit.Test;

import java.io.IOException;

import static org.junit.Assert.*;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {

  private static String TESTSTRING = "; This example illustrates basic arithmetic and \n" +
      "; uninterpreted functions\n" +
      "\n" +
      "(declare-fun x () Int)\n" +
      "(declare-fun y () Int)\n" +
      "(declare-fun z () Int)\n" +
      "(assert (>= (* 2 x) (+ y z)))\n" +
      "(declare-fun f (Int) Int)\n" +
      "(declare-fun g (Int Int) Int)\n" +
      "(assert (< (f x) (g x x)))\n" +
      "(assert (> (f y) (g x x)))\n" +
      "(check-sat)\n" +
      "(get-model)\n" +
      "(push)\n" +
      "(assert (= x y))\n" +
      "(check-sat)\n" +
      "(pop)\n" +
      "(exit)";

  @Test
  public void testTask(){
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    TextArea root = new TextArea();
    try {
      Z3Solver.concretize(TESTSTRING,
          optionalOutput -> root.appendText(optionalOutput.orElse("Something went wrong!"))
      );
    } catch (IOException e) {
      e.printStackTrace();
    }
    return new Scene(root, 800, 600);
  }
}