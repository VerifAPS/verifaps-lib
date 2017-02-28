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
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;

import java.util.*;

/**
 * Created by csicar on 13.02.17.
 */
public class SmtConcretizerTest {


  private List<ValidFreeVariable> freeVariables;

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
    ConstraintSpecificationValidator validator = new ConstraintSpecificationValidator(
        new SimpleObjectProperty<>(typeContext),
        new SimpleObjectProperty<>(codeIoVariables),
        new ReadOnlyObjectWrapper<>(freeVariables),
        constraintSpec);
    List<SpecProblem> specProblems = validator.problemsProperty().get();
    specProblems.stream().map(SpecProblem::getErrorMessage).forEach(System.out::println);

    return validator.getValidSpecification();
  }

  @Test
  public void simpleTest() throws Exception {

    ValidSpecification spec = importSpec("testSpec.xml");

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 7);
      put(1, 1);
      put(2, 2);
    }};

    SmtConcretizer concretizer = new SmtConcretizer(GlobalConfig.autoloadConfig());
    concretizer
        .calculateConcreteSpecification(spec, freeVariables, System.out::println, Throwable::printStackTrace);
  }

}