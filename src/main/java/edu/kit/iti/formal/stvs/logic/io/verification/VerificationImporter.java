package edu.kit.iti.formal.stvs.logic.io.verification;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.Importer;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;

import java.io.InputStream;

/**
 * Created by bal on 09.01.17.
 */
public class VerificationImporter implements Importer<VerificationResult> {

    @Override
    public VerificationResult doImport(InputStream source) throws ImportException {
        return null;
    }
}
