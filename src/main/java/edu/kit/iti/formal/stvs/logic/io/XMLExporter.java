package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.history.History;
import edu.kit.iti.formal.stvs.model.io.TestCase;
import org.w3c.dom.Node;

/**
 * Created by csicar on 09.01.17.
 */
public class XMLExporter {
    public Node exportSession(Code code, Collection<SpecificationTable> specs, GlobalConfig config, History history) {
        return null;
    }

    public Node exportVerificationScenario(TestCase testCase) {
        return null;
    }

    public Node exportTable(SpecificationTable table) {
        return null;
    }

    public Node exportConfig(GlobalConfig config) {
        return null;
    }

    public Node exportHistory(History history) {
        return null;
    }

    public void writeToFile(Node xml, String filename) {
        return null;
    }
}
