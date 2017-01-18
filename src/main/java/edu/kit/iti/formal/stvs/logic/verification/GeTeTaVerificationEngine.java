package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.verification.VerificationExporter;
import edu.kit.iti.formal.stvs.logic.io.verification.VerificationImporter;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.util.function.Consumer;

/**
 * Created by csicar on 11.01.17.
 * Handles communication with the ExTeTa verification engine
 */
public class GeTeTaVerificationEngine implements VerificationEngine {
  private VerificationExporter exporter;
  private VerificationImporter importer;
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
  public void addVerificationFinishedListener(Consumer<VerificationResult> verificationFinishedListener) {

  }

  @Override
  public void cancelVerification() {

  }


}
