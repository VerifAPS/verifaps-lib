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
    Z3Solver.concretizeSConstraint(preprocessor.getConstrain(), spec.getColumnHeaders(), System.out::println);
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
    Z3Solver.concretizeSConstraint(preprocessor.getConstrain(), spec.getColumnHeaders(), System.out::println);
  }
}