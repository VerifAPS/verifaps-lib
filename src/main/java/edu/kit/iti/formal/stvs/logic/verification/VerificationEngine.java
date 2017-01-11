package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.VerificationExporter;
import edu.kit.iti.formal.stvs.logic.io.VerificationImporter;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.io.VerificationScenario;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
//import edu.kit.iti.formal.automation.testtables; //TODO this doesn't import despite Maven repo

import java.util.function.Consumer;

/**
 * Strategy for Verification of the VerificationScenario
 */
public interface VerificationEngine {

    /**
     * Starts a verification in its own thread
     *
     * @param scenario scenario that should be checked
     */
    public void startVerification(VerificationScenario scenario);

    public void addVerificationFinishedListener(Consumer<VerificationResult> verificationFinishedListener);

    public void cancelVerification();
}
