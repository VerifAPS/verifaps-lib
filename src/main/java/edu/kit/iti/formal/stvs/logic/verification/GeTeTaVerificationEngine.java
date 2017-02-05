package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import javafx.beans.property.SimpleObjectProperty;

import java.util.function.Consumer;

/**
 * Created by csicar on 11.01.17.
 * Handles communication with the ExTeTa verification engine
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private GeTeTaExporter exporter;
  private GeTeTaImporter importer;
  private VerificationResult result;
  private Consumer<VerificationResult> verificationFinishedListener;
  //private ExTeTa exteta;


  public GeTeTaVerificationEngine() {

  }

  ;

  @Override
  public void startVerification(VerificationScenario scenario) {

  }

  @Override
  public OptionalProperty<VerificationResult> getVerificationResultProperty() {
    // TODO: write full implementation. This is just a pseudo-implementation!!
    return new OptionalProperty<VerificationResult>(new SimpleObjectProperty<>());
  }

  @Override
  public VerificationResult getVerificationResult() {
    return null;
  }

  @Override
  public void cancelVerification() {

  }


}
