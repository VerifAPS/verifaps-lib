package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.io.VerificationScenario;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import org.w3c.dom.Node;

import java.util.Collection;

/**
 * Created by csicar on 09.01.17.
 */
public class XMLExporter {
    public Node exportSession(Code code, Collection<SpecificationTable> specs, GlobalConfig config, History history) {
        return null;
    }

    public Node exportVerificationScenario(VerificationScenario testCase) {
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
    }
}
