package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;
import org.reactfx.value.Val;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtPreprocessorTest {
  @Test
  public void test() {
    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 2);
      put(1, 5);
      put(2, 5);
    }};

    Map<String, Type> typeContext = new HashMap<String,
        Type>() {{
      put("A", TypeInt.INT);
    }};
    ValidSpecification validSpecification = new ValidSpecification(new SimpleObjectProperty<>
        (typeContext.entrySet().stream().map(Map.Entry::getValue).collect(Collectors.toList
            ())), new FreeVariableSet());

    //validSpecification.getRows().addAll(new SpecificationRow<Expression>())
    SmtPreprocessor preprocessor = new SmtPreprocessor(maxDurations, validSpecification);
    System.out.println(preprocessor.getConstrain());
  }

  private ValidSpecification importSpec(String name) throws ImportException {
    return ImporterFacade.importSpec(getClass().getResourceAsStream(name), ImporterFacade
        .ImportFormat.XML).getValidSpecification();
  }

  @Test
  public void testImported() throws ImportException {
    ConstraintSpecification constraintSpecification = ImporterFacade.importSpec(getClass()
            .getResourceAsStream
            ("testSpec.xml"),
        ImporterFacade.ImportFormat.XML);
    System.out.println(constraintSpecification);
    ValidSpecification spec = constraintSpecification.getValidSpecification();

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 7);
      put(1, 1);
      put(2, 2);
    }};
    assertNotNull(spec.getSpecIoVariables());
    System.out.println(spec.getSpecIoVariables());
    SmtPreprocessor preprocessor = new SmtPreprocessor(maxDurations, spec);
    System.out.println(preprocessor.getConstrain());
  }

  public void testSimpleExample() throws ImportException {

  }
}