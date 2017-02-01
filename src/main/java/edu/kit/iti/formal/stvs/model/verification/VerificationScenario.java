package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.verification.GeTeTaVerificationEngine;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

/**
 * @author Benjamin Alt
 */
public class VerificationScenario {
  private OptionalProperty<VerificationResult> verificationResult;
  private VerificationEngine verificationEngine;
  private Code code;
  private VerificationState verificationState;

  public VerificationScenario() {
    code = new Code();
    verificationResult = new OptionalProperty<>(new SimpleObjectProperty<>());
    verificationEngine = new GeTeTaVerificationEngine();
    verificationEngine.getVerificationResultProperty().addListener(new
        VerificationChangedListener());
    verificationState = VerificationState.NOT_STARTED;
  }

  public VerificationScenario(Code code) {
    this.code = code;
    verificationEngine.getVerificationResultProperty().addListener(new
        VerificationChangedListener());
    verificationState = VerificationState.NOT_STARTED;
  }

  public void verify(ConstraintSpecification spec) {
    verificationEngine.startVerification(this);
    verificationState = VerificationState.RUNNING;
  }

  public void cancel() {
    verificationEngine.cancelVerification();
    verificationState = VerificationState.CANCELLED;
  }

  public VerificationState getVerificationState() {
    return verificationState;
  }

  public Code getCode() {
    return code;
  }

  public void setCode(Code code) {
    this.code = code;
  }

  public VerificationResult getVerificationResult() {
    return verificationResult.get();
  }

  public OptionalProperty<VerificationResult> verificationResultProperty() {
    return verificationResult;
  }

  private class VerificationChangedListener implements ChangeListener<VerificationResult> {
    @Override
    public void changed(ObservableValue<? extends VerificationResult> observableValue,
        VerificationResult oldResult, VerificationResult newResult) {
      verificationResult.set(newResult);
      verificationState = VerificationState.FINISHED;
    }
  }
}
