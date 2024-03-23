package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.TestUtils;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import javafx.beans.value.ObservableValue;
import junit.framework.AssertionFailedError;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

/**
 * Created by bal on 26.02.17.
 */
public class VerificationScenarioTest {
  private static final long TIMEOUT = 5000;
  private VerificationScenario scenario;
  private ConstraintSpecification constraintSpec;
  private GlobalConfig config;
  private Code code;
  private volatile boolean done;

  @Before
  public void setUp() throws URISyntaxException, IOException, ImportException {
    TestUtils.assumeNuXmvExists();
    TestUtils.assumeGetetaExists();

    scenario = new VerificationScenario();
    code = ImporterFacade.importStCode(new File(StvsApplication.class.getResource
        ("testSets/valid_1/code_valid_1.st").toURI()));
    constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
            .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
        ImporterFacade.ImportFormat.XML);
    scenario.setCode(code);
    config = GlobalConfig.autoloadConfig();
  }

  @Test(timeout=VerificationScenarioTest.TIMEOUT)
  public void testVerify() throws Exception {
    scenario.verificationResultProperty().addListener(new VerificationResultListener());
    assertEquals(VerificationState.NOT_STARTED, scenario.verificationState().get());
    scenario.verify(config, constraintSpec);
    assertEquals(VerificationState.RUNNING, scenario.verificationState().get());
    done = false;
    long startTime = System.currentTimeMillis();
    while (!done) {
      Thread.sleep(500);
    }
  }

  @Test
  public void testCancel() throws Exception {
    assertEquals(VerificationState.NOT_STARTED, scenario.verificationState().get());
    scenario.verify(config, constraintSpec);
    assertEquals(VerificationState.RUNNING, scenario.verificationState().get());
    scenario.cancel();
    assertEquals(VerificationState.CANCELLED, scenario.verificationState().get());
  }

  @Test
  public void testGetCode() throws Exception {
    assertEquals(code, scenario.getCode());
  }

  @Test
  public void testSetCode() throws Exception {
    VerificationScenario emptyScenario = new VerificationScenario();
    assertEquals(new Code(), emptyScenario.getCode());
    emptyScenario.setCode(code);
    assertEquals(code, emptyScenario.getCode());
  }

  @Test
  public void testGetSetActiveSpec() throws Exception {
    assertNull(scenario.getActiveSpec());
    scenario.setActiveSpec(constraintSpec);
    assertEquals(constraintSpec, scenario.getActiveSpec());
  }

  private class VerificationResultListener implements javafx.beans.value
      .ChangeListener<VerificationResult> {

    @Override
    public void changed(ObservableValue<? extends VerificationResult> observableValue,
                        VerificationResult old, VerificationResult newResult) {
      List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL, TypeFactory.enumOfName
          ("enumD", "literalOne", "literalTwo"));
      try {
        ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(StvsApplication
                .class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml"),
            ImporterFacade.ImportFormat.XML);
        VerificationResult expectedResult = ImporterFacade.importVerificationResult(StvsApplication
            .class.getResourceAsStream("testSets/valid_1/geteta_report_valid_1.xml"), ImporterFacade
            .ImportFormat.GETETA, typeContext, constraintSpec);
        /* Cannot just assertEquals() with verificationResults, as logFileNames (randomly
        generated) will be different
        assertEquals(expectedResult, newResult); */
        assertEquals(expectedResult.getClass(), newResult.getClass());
      } catch (ImportException e) {
        throw new AssertionFailedError();
      }
      done = true;
    }
  }
}