package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.verification.GeTeTaVerificationEngine;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.io.IOException;

/**
 * @author Benjamin Alt
 */
public class VerificationScenario {
  private OptionalProperty<VerificationResult> verificationResult;
  private VerificationEngine verificationEngine;
  private ObjectProperty<Code> code;
  private ObjectProperty<VerificationState> verificationState;

  public VerificationScenario() {
    this(new Code());
  }

  public VerificationScenario(Code code) {
    this.code = new SimpleObjectProperty<>(code);
    verificationResult = new OptionalProperty<>(new SimpleObjectProperty<>());
    verificationEngine = new GeTeTaVerificationEngine();
    verificationEngine.verificationResultProperty().addListener(new
        VerificationChangedListener());
    verificationState = new SimpleObjectProperty<>(VerificationState.NOT_STARTED);
  }

  public void verify(ConstraintSpecification spec) throws IOException, ExportException {
    verificationEngine.startVerification(this, spec);
    verificationState.set(VerificationState.RUNNING);
  }

  public void cancel() {
    verificationEngine.cancelVerification();
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

  public ObjectProperty<Code> codeObjectProperty() {
    return this.code;
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
      verificationState.set(VerificationState.FINISHED);
    }
  }
}
