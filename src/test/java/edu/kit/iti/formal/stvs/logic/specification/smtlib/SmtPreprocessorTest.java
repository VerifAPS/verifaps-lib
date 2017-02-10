package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblemRecognizer;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;

import java.util.*;
import java.util.stream.Collectors;

import static org.junit.Assert.assertNotNull;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtPreprocessorTest {

  private ValidSpecification importSpec(String name, List<ValidFreeVariable> freeVariables) throws
      ImportException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, new TypeEnum("colors",
        Arrays.asList("red", "green", "blue")));
    List<CodeIoVariable> codeIoVariables = new LinkedList<>();

    ConstraintSpecification constraintSpec = ImporterFacade.importSpec(getClass().getResourceAsStream(name), ImporterFacade
        .ImportFormat.XML);
    SpecProblemRecognizer recognizer = new SpecProblemRecognizer(
        new SimpleObjectProperty<>(typeContext), new SimpleObjectProperty<>(codeIoVariables),
        new SimpleObjectProperty<>(freeVariables), constraintSpec);
    return recognizer.getValidSpecification();
  }

  @Test
  public void testImported() throws ImportException {
    List<ValidFreeVariable> freeVariables = new LinkedList<>();

    ValidSpecification spec = importSpec("testSpec.xml", freeVariables);

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 7);
      put(1, 1);
      put(2, 2);
    }};

    SmtPreprocessor preprocessor = new SmtPreprocessor(maxDurations, spec, freeVariables);
    System.out.println(preprocessor.getConstrain());
  }

  public void testSimpleExample() throws ImportException {

  }
}