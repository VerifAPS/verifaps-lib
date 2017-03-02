package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.Performance;
import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.experimental.theories.suppliers.TestedOn;
import org.mockito.Mockito;

import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Method;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by csicar on 09.02.17.
 */
public class SmtEncoderTest {

  @Test
  //! Should take about 19min!
  @Category(Performance.class)
  public void performanceTest() {
    Supplier<InputStream> sourceFileGetter = () ->
        SmtEncoderTest.class.getResourceAsStream("spec_long_example.xml");
    ValidSpecification validSpec = TestUtils.importValidSpec(sourceFileGetter.get());

    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(
        sourceFileGetter.get());

    SmtEncoder smtEncoder = new SmtEncoder(3000, validSpec, freeVariables);
    SmtModel model = smtEncoder.getConstraint();

    List<SExpression> constrains = model.getGlobalConstraints();
    System.out.println(model.toString());
  }

  @Test
  //! Takes about 3min!
  @Category(Performance.class)
  public void performanceSingleVariableTest() {
    Supplier<InputStream> sourceFileGetter = () ->
        SmtEncoderTest.class.getResourceAsStream("spec_long_single_variable_example.xml");
    ValidSpecification validSpec = TestUtils.importValidSpec(sourceFileGetter.get());

    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(
        sourceFileGetter.get());

    SmtEncoder smtEncoder = new SmtEncoder(3000, validSpec, freeVariables);
    SmtModel model = smtEncoder.getConstraint();

    Collection<SExpression> constrains = model.getGlobalConstraints();
    Collection<SExpression> header = model.getVariableDefinitions();
    System.out.println(model.toString());
    System.out.println(model.toText().length());
    System.out.println(header);
  }

  @Test
  public void testNoDuplicateDefinition() {
    Supplier<InputStream> sourceFile = () -> XmlSessionImporterTest.class.getResourceAsStream(
        "spec_constraint_valid_enum_1.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SmtModel output = smtEncoder.getConstraint();
    Collection<SExpression> definitions = output.getDistinctVariableDefinitions();
    Set<SExpression> nonDuplicate = new LinkedHashSet<>(definitions);
    assertEquals(nonDuplicate, definitions);
  }

  @Test
  public void testEnums1() {
    Supplier<InputStream> sourceFile = () -> XmlSessionImporterTest.class.getResourceAsStream(
        "spec_constraint_valid_enum_1.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();

    System.out.println(output.toString());

    testWithStatements(constraints,
        "( bvsge |lala_2_2| #x0000 )",
        "( bvslt |lala_2_2| #x0003 )",
        "( bvsge |lala_2_1| #x0000 )",
        "( bvslt |lala_2_1| #x0003 )",
        "( bvsge |lala_2_0| #x0000 )",
        "( bvslt |lala_2_0| #x0003 )",
        "( bvsge |lala_1_0| #x0000 )",
        "( bvslt |lala_1_0| #x0003 )",
        "( bvsge |lala_0_2| #x0000 )",
        "( bvslt |lala_0_2| #x0003 )",
        "( bvsge |lala_0_1| #x0000 )",
        "( bvslt |lala_0_1| #x0003 )",
        "( bvsge |lala_0_0| #x0000 )",
        "( bvslt |lala_0_0| #x0003 )");
  }

  @Test
  public void testEnums2() {
    Supplier<InputStream> sourceFile = () -> XmlSessionImporterTest.class.getResourceAsStream(
        "spec_constraint_valid_enum_1.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue", "orange", "black")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();

    System.out.println(output.toString());

    testWithStatements(constraints,
        "( bvsge |lala_2_2| #x0000 )",
        "( bvslt |lala_2_2| #x0005 )",
        "( bvsge |lala_2_1| #x0000 )",
        "( bvslt |lala_2_1| #x0005 )",
        "( bvsge |lala_2_0| #x0000 )",
        "( bvslt |lala_2_0| #x0005 )",
        "( bvsge |lala_1_0| #x0000 )",
        "( bvslt |lala_1_0| #x0005 )",
        "( bvsge |lala_0_2| #x0000 )",
        "( bvslt |lala_0_2| #x0005 )",
        "( bvsge |lala_0_1| #x0000 )",
        "( bvslt |lala_0_1| #x0005 )",
        "( bvsge |lala_0_0| #x0000 )",
        "( bvslt |lala_0_0| #x0005 )");
  }

  @Test
  public void testNotEquals() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_all.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue", "orange", "black")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();

    System.out.println(output.toString());


    testWithStatements(constraints,
        "( implies ( bvuge n_1 #x0000 ) ( not ( = |C_1_0| #x0032 ) ) )");
  }

  @Test
  public void testGetMaxDurations() throws Exception {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_all.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue", "orange", "black")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    Class<?>[] args = new Class<?>[1];
    args[0] = int.class;
    Method getMaxDurations= smtEncoder.getClass().getDeclaredMethod("getMaxDuration", args);
    getMaxDurations.setAccessible(true);
    assertEquals(0, getMaxDurations.invoke(smtEncoder, -1));
    assertEquals(0, getMaxDurations.invoke(smtEncoder, -100));
    assertEquals(3, getMaxDurations.invoke(smtEncoder, 0));
    assertEquals(1, getMaxDurations.invoke(smtEncoder, 1));
  }

  @Test
  public void testUnsupportedOperation() {

  }

  @Test(expected = IllegalStateException.class)
  public void testMismatchingUsedVariablesAndVariableDefinitions() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_freevariable.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum(
        "Color",
        Arrays.asList("red", "green", "blue")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get(),
        new TypeEnum("Color",
            Arrays.asList("red", "green", "blue")));

    int maxDuration = 5;


    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, Collections.emptyList());
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();
    Collection<SExpression> definitions = output.getVariableDefinitions();



  }

  @Test(expected = IllegalArgumentException.class)
  public void testDifferentLengthInputs() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_all.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get(), new TypeEnum("colors",
        Arrays.asList("red", "green", "blue", "orange", "black")));
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    SmtEncoder smtEncoder = new SmtEncoder(Collections.singletonList(3), spec, freeVariables);
  }

  @Test
  public void testMjSmallerDuration() {
    Supplier<InputStream> sourceFile = () -> SmtEncoderTest.class.getResourceAsStream(
        "spec_constant.xml");

    ValidSpecification spec = TestUtils.importValidSpec(sourceFile.get());
    List<ValidFreeVariable> freeVariables = TestUtils.importValidFreeVariables(sourceFile.get());

    int maxDuration = 3;

    SmtEncoder smtEncoder = new SmtEncoder(maxDuration, spec, freeVariables);
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();


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
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();
    Collection<SExpression> definitions = output.getVariableDefinitions();

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
    SmtModel output = smtEncoder.getConstraint();
    List<SExpression> constraints = output.getGlobalConstraints();
    Collection<SExpression> definitions = output.getVariableDefinitions();

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
    SmtModel output = smtEncoder.getConstraint();
    Collection<SExpression> constraints = output.getGlobalConstraints();

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

  private void testWithStatements(Collection<SExpression> constraints, String... s) {
    List<SExpression> statements = Arrays.stream(s).map(SExpression::fromText)
        .collect
            (Collectors
                .toList());

    List<SExpression> missingStatements = statements.stream().filter
        (statement
            -> !constraints
            .contains
                (statement))
        .collect(Collectors.toList());

    assertEquals("no statements should be missing", new ArrayList<SExpression>(), missingStatements);
  }

}