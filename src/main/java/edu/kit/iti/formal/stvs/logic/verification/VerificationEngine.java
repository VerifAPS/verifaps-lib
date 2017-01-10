package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.VerificationExporter;
import edu.kit.iti.formal.stvs.logic.io.VerificationImporter;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
//import edu.kit.iti.formal.automation.testtables; //TODO this doesn't import despite Maven repo

import java.util.function.Consumer;

/**
 * Handles communication with the ExTeTa verification engine
 */
public class VerificationEngine {
    private VerificationExporter exporter;
    private VerificationImporter importer;
    private VerificationResult result;
    private Consumer<VerificationResult> verificationFinishedListener;
    //private ExTeTa exteta;

    public VerificationEngine(Consumer<VerificationResult> verificationFinishedListener) {

    }

    /**
     * Starts a verification in its own thread
     * @param code The code to verify
     * @param spec The specification to verify against
     */
    public void startVerification(Code code, ConstraintSpecification spec) {

    }
}
