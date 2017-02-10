package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;
import org.reactfx.value.Val;

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

  @Test
  public void testImported() throws ImportException {
    ValidSpecification spec = ImporterFacade.importSpec(getClass().getResourceAsStream("testSpec.xml"), ImporterFacade.ImportFormat.XML).getValidSpecification();
    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 2);
      put(1, 2);
      put(2, 4);
    }};
    SmtPreprocessor preprocessor = new SmtPreprocessor(maxDurations, spec);
    System.out.println(preprocessor.getConstrain());
  }
}