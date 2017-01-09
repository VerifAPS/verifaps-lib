package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.code.Code;
import org.w3c.dom.Node;

/**
 * Created by csicar on 09.01.17.
 */
public class XMLExporter {
    public Node exportSession(Code code, Collection<SpecificationTable> specs, Config config, History history) {
        return null;
    }

    public Node exportVerificationScenario(TestCase testCase) {
        return null;
    }

    public Node exportTable(SpecificationTable table) {
        return null;
    }

    public Node exportConfig(Config config) {
        return null;
    }

    public Node exportHistory(History history) {
        return null;
    }

    public void writeToFile(Node xml, String filename) {
        return null;
    }
}
