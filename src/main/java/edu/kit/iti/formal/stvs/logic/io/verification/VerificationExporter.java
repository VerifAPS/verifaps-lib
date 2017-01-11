package edu.kit.iti.formal.stvs.logic.io.verification;

import edu.kit.iti.formal.stvs.logic.io.Exporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XMLSpecExporter;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import java.io.OutputStream;

/**
 * Created by bal on 09.01.17.
 */
public class VerificationExporter implements Exporter<ConstraintSpecification> {

    private XMLSpecExporter xmlExporter;

    public VerificationExporter() {

    }

    public  OutputStream export(ConstraintSpecification source) {
        return null;
    }
}
