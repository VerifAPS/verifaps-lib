package edu.kit.iti.formal.stvs.logic.verification;

import edu.kit.iti.formal.stvs.logic.io.VerificationExporter;
import edu.kit.iti.formal.stvs.logic.io.VerificationImporter;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.io.VerificationScenario;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;

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


    public GeTeTaVerificationEngine(Consumer<VerificationResult> verificationFinishedListener) {

    };

    @Override
    public void startVerification(VerificationScenario scenario) {

    }

    @Override
    public void cancelVerification() {

    }


}
