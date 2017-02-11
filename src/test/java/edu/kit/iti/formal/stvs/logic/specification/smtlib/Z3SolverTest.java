package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.util.AsyncTask;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.control.TextArea;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {

  private static String TESTSTRING = "; This example illustrates basic arithmetic and \n" +
      "; uninterpreted functions\n" +
      "\n" +
      "(declare-fun A_0_0 () Int)\n" +
      "(declare-fun B_0_0 () Int)\n" +
      "(declare-fun A_1_0 () Int)\n" +

      "(check-sat)\n" +
      "(get-model)\n" +
      "(exit)";

  private static String TEST2 = "(declare-const A_0_0 Int)\n" +
      "(declare-const B_0_0 Bool)\n" +
      "(declare-const n_0 Int)\n" +
      "(assert (= A_0_0 10))\n" +
      "(assert (= n_0 1))\n" +
      "(check-sat)\n" +
      "(get-value (A_0_0 B_0_0 n_0))";

  @Test
  public void testTask() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    TextArea root = new TextArea();
    List<ValidIoVariable> validIoVariables = new ArrayList<>();
    validIoVariables.add(new ValidIoVariable(VariableCategory.INPUT, "A", TypeInt.INT));
    validIoVariables.add(new ValidIoVariable(VariableCategory.OUTPUT, "B", TypeBool.BOOL));
    AsyncTask<Optional<ConcreteSpecification>> asysncTask = new AsyncTask<>(
        () -> {
          Optional<ConcreteSpecification> concrete = Optional.empty();
          try {
            concrete = Z3Solver.concretizeVarAssignment(TEST2, validIoVariables);
          } catch (IOException e) {
            e.printStackTrace();
          }
          return concrete;
        },
        (optionalConcreteSpec) -> System.out.println(optionalConcreteSpec)
    );
    asysncTask.run();
    return new Scene(root, 800, 600);
  }
}