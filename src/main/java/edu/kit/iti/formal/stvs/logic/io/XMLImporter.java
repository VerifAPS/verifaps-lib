package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.history.History;
import edu.kit.iti.formal.stvs.model.io.VerificationScenario;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import org.w3c.dom.Node;

/**
 * Created by csicar on 09.01.17.
 */
public class XMLImporter {
    public Node readFromFile(String fileName) {
        return null;
    }

    public VerificationScenario importVerificationScenario(Node node) throws ImportException {
        return null;
    }

    public SpecificationTable importTable(Node node) throws ImportException {
        return null;
    }

    public GlobalConfig importConfig(Node node) throws ImportException {
        return null;
    }

    public History importHistory(Node node) throws ImportException {
        return null;
    }
}
