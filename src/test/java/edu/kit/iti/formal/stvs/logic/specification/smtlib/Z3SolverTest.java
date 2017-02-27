package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {

  static {
    System.out.println("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
    System.out.println(System.getProperty("user.home"));
  }

  private List<ValidFreeVariable> freeVariables;
  private final Z3Solver solver = new Z3Solver(GlobalConfig.autoloadConfig());

  public Z3SolverTest() throws ImportException {
  }

  private ValidSpecification importSpec(String name) throws
      ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, new TypeEnum("colors",
        Arrays.asList("red", "green", "blue")));
    List<CodeIoVariable> codeIoVariables = new LinkedList<>();

    ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(getClass().getResourceAsStream(name), ImporterFacade
        .ImportFormat.XML);
    FreeVariableListValidator freeVariableListValidator = new FreeVariableListValidator(new
        SimpleObjectProperty<>(typeContext), constraintSpec
        .getFreeVariableList());
    List<ValidFreeVariable> freeVariables = freeVariableListValidator.validFreeVariablesProperty().get();
    this.freeVariables = freeVariables;
    ConstraintSpecificationValidator recognizer = new ConstraintSpecificationValidator(
        new SimpleObjectProperty<>(typeContext),
        new SimpleObjectProperty<>(codeIoVariables),
        new ReadOnlyObjectWrapper<>(freeVariables),
        constraintSpec);
    List<SpecProblem> specProblems = recognizer.problemsProperty().get();
    specProblems.stream().map(SpecProblem::getErrorMessage).forEach(System.err::println);

    return recognizer.getValidSpecification();
  }

  @Test
  public void testImported() throws ImportException, IOException, InterruptedException {

    ValidSpecification spec = importSpec("testSpec.xml");

    List<Integer> maxDurations = new ArrayList<Integer>() {{
      add(7);
      add(1);
      add(2);
    }};
    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    AtomicBoolean outputProcessed = new AtomicBoolean(false);

    ProcessOutputAsyncTask processOutputAsyncTask = solver.concretizeSConstraint(preprocessor.getConstraint(),
        spec.getColumnHeaders(), optionalSpec -> {
          ConcreteSpecification concreteSpecification = optionalSpec.get();
          assertNotNull(concreteSpecification);
          ObservableList<ConcreteDuration> durations = concreteSpecification.getDurations();
          assertTrue(durations.get(0).getDuration() >= 5 && durations.get(0).getDuration() <= 7);
          assertEquals(1, durations.get(1).getDuration());
          assertEquals(2, durations.get(2).getDuration());
          outputProcessed.set(true);
        });
    processOutputAsyncTask.start();
    processOutputAsyncTask.join();
    assertTrue(outputProcessed.get());
  }
}