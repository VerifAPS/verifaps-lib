package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import org.apache.commons.collections4.queue.CircularFifoQueue;

import java.util.List;

public class STVSRootModel {

    private List<HybridSpecification> hybridSpecifications;
    private GlobalConfig globalConfig;
    private History history;
    private VerificationScenario scenario;

    public STVSRootModel() {

    }

    public List<HybridSpecification> getHybridSpecifications() {
        return hybridSpecifications;
    }

    public GlobalConfig getGlobalConfig() {
        return globalConfig;
    }

    public History getHistory() {
        return history;
    }

    public VerificationScenario getScenario() {
        return scenario;
    }
}
