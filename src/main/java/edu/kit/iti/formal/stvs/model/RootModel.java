package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.history.History;

public class RootModel {
    private HashSet<HybridSpecification> hybridSpecifications;
    private GlobalConfig globalConfig;
    private History history;

    public RootModel() {

    }

    public HashSet<HybridSpecification> getHybridSpecifications() {
        return hybridSpecifications;
    }

    public GlobalConfig getGlobalConfig() {
        return globalConfig;
    }

    public History getHistory() {
        return history;
    }
}
