package edu.kit.iti.formal.stvs.model.verification;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.verification.GeTeTaVerificationEngine;
import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine;
import edu.kit.iti.formal.stvs.logic.verification.VerificationException;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.io.IOException;

/**
 * @author Benjamin Alt
 */
public class VerificationScenario {
  private NullableProperty<VerificationResult> verificationResult;
  private VerificationEngine verificationEngine;
  private ObjectProperty<Code> code;
  private ObjectProperty<VerificationState> verificationState;

  public VerificationScenario() {
    this(new Code());
  }

  public VerificationScenario(Code code) {
    this.code = new SimpleObjectProperty<>(code);
    verificationResult = new NullableProperty<>();
    verificationState = new SimpleObjectProperty<>(VerificationState.NOT_STARTED);
  }

  public void verify(String getetaFilename, String nuxmvFilename, ConstraintSpecification spec)
      throws IOException,
      ExportException, VerificationException {
    verificationEngine = new GeTeTaVerificationEngine(getetaFilename, nuxmvFilename, code.get()
        .getParsedCode()
        .getDefinedTypes());
    verificationEngine.verificationResultProperty().addListener(new
        VerificationChangedListener());
    verificationState = new SimpleObjectProperty<>(VerificationState.NOT_STARTED);
    verificationEngine.startVerification(this, spec);
    verificationState.set(VerificationState.RUNNING);
  }

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
