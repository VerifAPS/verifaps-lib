package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import org.junit.Test;

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
  public void testMjSmallerDuration() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_constant.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SConstraint output = smtEncoder.getConstraint();
    Set<SExpr> constraints = output.getGlobalConstraints();

    System.out.println(output.toString());

    testWithStatements(constraints,
        "( bvuge n_0 #x0005 )",
        " ( bvule n_0 #x0003 )  ",
        "( implies  ( bvuge n_0 #x0000 )   ( = |C_0_0| #x002A )  )",
        " ( implies  ( bvuge n_0 #x0001 )   ( = |C_0_1| #x002A )  )",
        "( implies  ( bvuge n_0 #x0002 )   ( = |C_0_2| #x002A )  )");

  }

  @Test
  public void testFreeVariablesDefaultValue() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_freevariable.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum(
        "Color",
        Arrays.asList("red", "green", "blue")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get(),
        new TypeEnum("Color",
            Arrays.asList("red", "green", "blue")));

    int maxDuration = 50;



    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SConstraint output = smtEncoder.getConstraint();
    Set<SExpr> constraints = output.getGlobalConstraints();
    Set<SExpr> definitions = output.getVariableDefinitions();

    System.out.println(output.toString());

    testWithStatements(definitions, "(assert (= |p| #x000F))");
    testWithStatements(definitions, "(assert (= |q| #x0001))");
    testWithStatements(definitions, "(assert (= |r| true))");

  }

  @Test
  public void testFreeVariablesDefaultValueSimple() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_freevars.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 50;



    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SConstraint output = smtEncoder.getConstraint();
    Set<SExpr> constraints = output.getGlobalConstraints();
    Set<SExpr> definitions = output.getVariableDefinitions();

    System.out.println(output.toString());
    System.out.println(output.toText());

    testWithStatements(definitions, "(assert (= |freevar| #x0000))");

  }

  @Test
  public void testImported() throws ImportException {
    Supplier<InputStream> sourceFile = () ->
        SmtEncoderTest.class.getResourceAsStream("testSpec.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    List<Integer> maxDurations = new ArrayList<Integer>() {{
      add(7);
      add(1);
      add(2);
    }};

    SmtEncoder preprocessor = new SmtEncoder(maxDurations, spec, freeVariables);
    System.out.println(preprocessor.getConstraint());
  }


  @Test
  public void testSimpleExample() throws ImportException, IOException {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "simpleBackwardsReferenceTestSpec.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    List<Integer> maxDurations = new ArrayList<Integer>() {{
      add(3);
      add(5);
      add(5);
    }};

    SmtEncoder smtEncoder = new SmtEncoder(maxDurations, spec, freeVariables);
    SConstraint output = smtEncoder.getConstraint();
    Set<SExpr> constraints = output.getGlobalConstraints();

    System.out.println(output);


    testWithStatements(constraints,
        "(implies (bvuge n_2  #x0004) (= |A_2_4| |A_2_0|))",

        "(implies (bvuge n_2  #x0003) (= |A_2_3| |A_2_-1|))",
        "(implies (= n_1  #x0001) (= |A_2_-1| |A_1_0|))",

        "(implies (bvuge n_2  #x0002) (= |A_2_2| |A_2_-2|))",
        "(implies (= n_1  #x0001) (= |A_2_-2| |A_1_-1|))",
        "(implies (= n_0  #x0003) (= |A_1_-1| |A_0_2|))",

        "(implies (bvuge n_2  #x0001) (= |A_2_1| |A_2_-3|))",
        "(implies (= n_1  #x0001) (= |A_2_-3| |A_1_-2|))",
        "(implies (= n_0  #x0003) (= |A_1_-2| |A_0_1|))",

        "(implies (bvuge n_2  #x0000) (= |A_2_0| |A_2_-4|))",
        "(implies (= n_1  #x0001) (= |A_2_-4| |A_1_-3|))",
        "(implies (= n_0  #x0003) (= |A_1_-3| |A_0_0|))");

    testWithStatements(constraints,
        "(implies (bvuge n_2  #x0004) (= |A_2_4| |A_2_0|))",

        "(implies (bvuge n_2  #x0003) (= |A_2_3| |A_2_-1|))",
        "(implies (= n_1  #x0002) (= |A_2_-1| |A_1_1|))",

        "(implies (bvuge n_2  #x0002) (= |A_2_2| |A_2_-2|))",
        "(implies (= n_1  #x0002) (= |A_2_-2| |A_1_0|))",

        "(implies (bvuge n_2  #x0001) (= |A_2_1| |A_2_-3|))",
        "(implies (= n_1  #x0002) (= |A_2_-3| |A_1_-1|))",
        "(implies (= n_0  #x0003) (= |A_1_-1| |A_0_2|))",


        "(implies (bvuge n_2  #x0000) (= |A_2_0| |A_2_-4|))",
        "(implies (= n_1  #x0002) (= |A_2_-4| |A_1_-2|))",
        "(implies (= n_0  #x0003) (= |A_1_-2| |A_0_1|))"
        );

    testWithStatements(constraints,
        "(bvuge n_0  #x0003)",
        "(bvule n_0  #x0003)",

        "(bvuge n_1  #x0001)",
        "(bvule n_1  #x0005)",

        "(bvuge n_2  #x0001)",
        "(bvule n_2  #x0005)"
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