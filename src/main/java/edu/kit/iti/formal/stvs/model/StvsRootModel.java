package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.util.List;

public class StvsRootModel {

  private List<HybridSpecification> hybridSpecifications;
  private GlobalConfig globalConfig;
  private History history;
  private VerificationScenario scenario;

  public StvsRootModel() {

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
