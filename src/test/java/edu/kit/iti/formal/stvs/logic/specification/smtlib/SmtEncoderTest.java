package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import javafx.beans.property.ReadOnlyObjectWrapper;
import javafx.beans.property.SimpleObjectProperty;
import org.junit.Test;
import org.junit.*;

import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtEncoderTest {

  @Test
  public void testImported() throws ImportException {
    Supplier<InputStream> sourceFile = () ->
        SmtEncoderTest.class.getResourceAsStream("testSpec.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 7);
      put(1, 1);
      put(2, 2);
    }};

    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    System.out.println(preprocessor.getConstrain());
  }


  @Test
  public void testSimpleExample() throws ImportException, IOException {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "simpleBackwardsReferenceTestSpec.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    Map<Integer, Integer> maxDurations = new HashMap<Integer,
        Integer>() {{
      put(0, 3);
      put(1, 5);
      put(2, 5);
    }};

    SmtEncoder smtEncoder = new SmtEncoder(maxDurations, spec, freeVariables);
    SConstraint output = smtEncoder.getConstrain();
    Set<SExpr> constraints = output.getGlobalConstraints();

    System.out.println(output);
    testWithStatements(constraints,
        "(implies (> n_2 4) (= |A_2_4| |A_2_0|))",

        "(implies (> n_2 3) (= |A_2_3| |A_2_-1|))",
        "(implies (= n_1 1) (= |A_2_-1| |A_1_0|))",

        "(implies (> n_2 2) (= |A_2_2| |A_2_-2|))",
        "(implies (= n_1 1) (= |A_2_-2| |A_1_-1|))",
        "(implies (= n_0 3) (= |A_1_-1| |A_0_2|))",

        "(implies (> n_2 1) (= |A_2_1| |A_2_-3|))",
        "(implies (= n_1 1) (= |A_2_-3| |A_1_-2|))",
        "(implies (= n_0 3) (= |A_1_-2| |A_0_1|))",

        "(implies (> n_2 0) (= |A_2_0| |A_2_-4|))",
        "(implies (= n_1 1) (= |A_2_-4| |A_1_-3|))",
        "(implies (= n_0 3) (= |A_1_-3| |A_0_0|))");

    testWithStatements(constraints,
        "(implies (> n_2 4) (= |A_2_4| |A_2_0|))",

        "(implies (> n_2 3) (= |A_2_3| |A_2_-1|))",
        "(implies (= n_1 2) (= |A_2_-1| |A_1_1|))",

        "(implies (> n_2 2) (= |A_2_2| |A_2_-2|))",
        "(implies (= n_1 2) (= |A_2_-2| |A_1_0|))",

        "(implies (> n_2 1) (= |A_2_1| |A_2_-3|))",
        "(implies (= n_1 2) (= |A_2_-3| |A_1_-1|))",
        "(implies (= n_0 3) (= |A_1_-1| |A_0_2|))",


        "(implies (> n_2 0) (= |A_2_0| |A_2_-4|))",
        "(implies (= n_1 2) (= |A_2_-4| |A_1_-2|))",
        "(implies (= n_0 3) (= |A_1_-2| |A_0_1|))"
        );

    testWithStatements(constraints,
        "(>= n_0 3)",
        "(<= n_0 3)",

        "(>= n_1 1)",
        "(<= n_1 5)",

        "(>= n_2 1)",
        "(<= n_2 5)"
    );
  }

  private void testWithStatements(Set<SExpr> constraints,String ... s) {
    List<SExpr> statements = Arrays.stream(s).map(SExpr::fromString)
        .collect
        (Collectors
        .toList());

    List<SExpr> missingStatements = statements.stream().filter
        (statement
            -> !constraints
            .contains
                (statement))
        .collect(Collectors.toList());

    assertEquals("no statements should be missing", new ArrayList<SExpr>(), missingStatements);
  }

}