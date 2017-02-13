package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Ignore;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

/**
 * Created by leonk on 09.02.2017.
 */
public class Z3SolverTest {

  private static String TEST2 = "(declare-const A_0_0 Int)\n" +
      "(declare-const B_0_0 Bool)\n" +
      "(declare-const n_0 Int)\n" +
      "(assert (= A_0_0 10))\n" +
      "(assert (= n_0 1))\n" +
      "(check-sat)\n" +
      "(get-value (A_0_0 B_0_0 n_0))";

  @Test
  @Ignore//Must be rewritten. Is now wrong.
  public void testSimpleConcretize() throws IOException {
    List<ValidIoVariable> validIoVariables = new ArrayList<>();
    validIoVariables.add(new ValidIoVariable(VariableCategory.INPUT, "A", TypeInt.INT));
    validIoVariables.add(new ValidIoVariable(VariableCategory.OUTPUT, "B", TypeBool.BOOL));
    Optional<ConcreteSpecification> concreteSpecificationOptional = Z3Solver.concretizeVarAssignment(TEST2, validIoVariables);
    System.out.println(concreteSpecificationOptional);
    assertTrue(concreteSpecificationOptional.isPresent());
    ConcreteSpecification concreteSpecification = concreteSpecificationOptional.get();
    assertEquals(1,concreteSpecification.getDurations().get(0).getDuration());
    assertEquals(10, ((ValueInt)concreteSpecification.getColumnByName("A").getCells().get(0).getValue()).getValue());
    assertNotNull(concreteSpecification.getColumnByName("B").getCells().get(0));
  }

  private List<ValidFreeVariable> freeVariables;

  private ValidSpecification importSpec(String name) throws
      ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, new TypeEnum("colors",
        Arrays.asList("red", "green", "blue")));
    List<CodeIoVariable> codeIoVariables = new LinkedList<>();

    ConstraintSpecification constraintSpec = ImporterFacade.importSpec(getClass().getResourceAsStream(name), ImporterFacade
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
  public void testImported() throws ImportException, IOException {

    ValidSpecification spec = importSpec("testSpec.xml");

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 7);
      put(1, 1);
      put(2, 2);
    }};

    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    //System.out.println(preprocessor.getConstrain());
    Optional<ConcreteSpecification> concreteSpecification = Z3Solver.concretizeSConstraint(preprocessor.getConstrain(), spec.getColumnHeaders());
    System.out.println(concreteSpecification);
  }

  @Test
  public void testImported2() throws ImportException, IOException {

    ValidSpecification spec = importSpec("spec_constraint_valid_enum_1.xml");

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 20);
      put(1, 20);
      put(2, 20);
    }};

    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    //System.out.println(preprocessor.getConstrain());
    Optional<ConcreteSpecification> concreteSpecification = Z3Solver.concretizeSConstraint(preprocessor.getConstrain(), spec.getColumnHeaders());
    System.out.println(concreteSpecification);
  }
}