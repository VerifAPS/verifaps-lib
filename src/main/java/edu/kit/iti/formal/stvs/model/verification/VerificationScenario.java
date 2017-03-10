package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.verification.GeTeTaVerificationEngine;
import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import java.io.IOException;

import edu.kit.iti.formal.stvs.util.ProcessCreationException;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

/**
 * The main model object for orchestrating a verification. Has a reference to the currently loaded
 * {@link Code}, uses a {@link VerificationEngine} from the logic package to verify it against a
 * {@link ConstraintSpecification} and provides access to the {@link VerificationResult}.
 *
 * @author Benjamin Alt
 */
public class VerificationScenario {
  private NullableProperty<VerificationResult> verificationResult;
  private VerificationEngine verificationEngine;
  private ObjectProperty<Code> code;
  private ObjectProperty<VerificationState> verificationState;
  private NullableProperty<ConstraintSpecification> activeSpec;

  /**
   * Constructs an empty VerificationScenario (with an empty code).
   */
  public VerificationScenario() {
    this(new Code());
  }

  /**
   * Constructs a VerificationScenario from a given {@link Code}.
   *
   * @param code The initial code
   */
  public VerificationScenario(Code code) {
    this.code = new SimpleObjectProperty<>(code);
    verificationResult = new NullableProperty<>();
    verificationState = new SimpleObjectProperty<>(VerificationState.NOT_STARTED);
    activeSpec = new NullableProperty<>();
  }

  /**
   * Starts a verification of the current {@link Code} against a given
   * {@link ConstraintSpecification}.
   *
   * @param config The config to take into account (i.e. for verification timeouts, paths to
   *        dependencies etc.)
   * @param spec The specification to be verified
   * @throws IOException Exception while IO interaction
   * @throws ExportException Exception while exporting
   */
  public void verify(GlobalConfig config, ConstraintSpecification spec)
      throws IOException, ExportException, ProcessCreationException {
    activeSpec.set(spec);
    verificationEngine =
        new GeTeTaVerificationEngine(config, code.get().getParsedCode().getDefinedTypes());
    verificationEngine.verificationResultProperty().addListener(new VerificationChangedListener());
    verificationState.setValue(VerificationState.RUNNING);
    verificationEngine.startVerification(this, spec);
  }

  /**
   * Stops a currently running verification.
   */
  public void cancel() {
    if (verificationEngine != null) {
      verificationEngine.cancelVerification();
    }
    verificationState.set(VerificationState.CANCELLED);
  }

  public ObjectProperty<VerificationState> verificationState() {
    return verificationState;
  }

  public Code getCode() {
    return code.get();
  }

  public void setCode(Code code) {
    this.code.set(code);

  }

  public ConstraintSpecification getActiveSpec() {
    return activeSpec.get();
  }

  public void setActiveSpec(ConstraintSpecification spec) {
    activeSpec.set(spec);
  }

  public NullableProperty<ConstraintSpecification> activeSpecProperty() {
    return activeSpec;
  }

  public ObjectProperty<Code> codeObjectProperty() {
    return this.code;
  }

  public VerificationResult getVerificationResult() {
    return verificationResult.get();
  }

  public NullableProperty<VerificationResult> verificationResultProperty() {
    return verificationResult;
  }

  private class VerificationChangedListener implements ChangeListener<VerificationResult> {
    @Override
    public void changed(ObservableValue<? extends VerificationResult> observableValue,
        VerificationResult oldResult, VerificationResult newResult) {
      verificationResult.set(newResult);
      verificationState.set(VerificationState.FINISHED);
    }
  }
}
