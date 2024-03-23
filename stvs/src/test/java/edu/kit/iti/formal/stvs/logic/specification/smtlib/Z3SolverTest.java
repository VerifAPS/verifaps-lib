package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.Performance;
import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException;
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
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {
  private List<ValidFreeVariable> freeVariables;

  private Z3Solver solver;

    @Before public void initialize() {
        this.solver = new Z3Solver(GlobalConfig.autoloadConfig());
        TestUtils.assumeZ3Exists();
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
  @Category(Performance.class)
  public void testLongExample() throws Exception {
    GlobalConfig config = GlobalConfig.autoloadConfig();
    Z3Solver solver = new Z3Solver(config);
    ValidSpecification spec = importSpec("spec_long_single_variable_example.xml");
    SmtEncoder encoder = new SmtEncoder(3000, spec, new ArrayList<>());

    System.out.println(encoder.getConstraint().toText());
    ConcreteSpecification concreteSpecification = solver.concretizeSmtModel(encoder.getConstraint(), spec.getColumnHeaders());
    assertNotNull(concreteSpecification);
  }

  @Test
  public void testImported() throws ImportException, IOException, InterruptedException, ConcretizationException {

    ValidSpecification spec = importSpec("testSpec.xml");

    List<Integer> maxDurations = new ArrayList<Integer>() {{
      add(7);
      add(1);
      add(2);
    }};
    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    ConcreteSpecification concretized = solver.concretizeSmtModel(preprocessor.getConstraint(), spec.getColumnHeaders());
    assertNotNull(concretized);
    ObservableList<ConcreteDuration> durations = concretized.getDurations();
    assertTrue(durations.get(0).getDuration() >= 5 && durations.get(0).getDuration() <= 7);
    assertEquals(1, durations.get(1).getDuration());
    assertEquals(2, durations.get(2).getDuration());
  }

  @Test
  public void getProcess() throws Exception {
    assertNull(solver.getProcess());

    ValidSpecification spec = importSpec("testSpec.xml");
    SmtEncoder preprocessor = new SmtEncoder(5, spec, freeVariables);
    solver.concretizeSmtModel(preprocessor.getConstraint(), spec.getColumnHeaders());

    assertNotNull(solver.getProcess());
  }

  @Test
  public void setZ3Path() throws Exception {
    solver.setZ3Path("testValue");
    assertEquals("testValue", solver.getZ3Path());
    solver.setZ3Path("otherValue");
    assertEquals("otherValue", solver.getZ3Path());
  }

  @Test
  @Ignore
  public void testTerminate() throws Exception {
    Thread thread = new Thread(() -> {
      try {
        ValidSpecification spec = importSpec("spec_long_single_variable_example.xml");
        SmtEncoder preprocessor = new SmtEncoder(5, spec, freeVariables);
        solver.concretizeSmtModel(preprocessor.getConstraint(), spec.getColumnHeaders());
        System.out.println("finished");
      } catch(Exception e) {
        e.printStackTrace();
        assertTrue(e instanceof ConcretizationException);
      }
    });
    thread.start();
    System.out.println("started");
    Thread.sleep(400);
    System.out.println("waiting for process");
    while (solver.getProcess() == null) {

    }
    System.out.println("interrupt");
    thread.interrupt();
    thread.join();

  }

  @Test
  public void concretizeSmtModel() throws Exception {

  }
}