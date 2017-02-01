package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class StvsRootModel {

  private List<HybridSpecification> hybridSpecifications;
  private GlobalConfig globalConfig;
  private History history;
  private VerificationScenario scenario;

  /**
   * Create a new empty StvsRootModel with no specifications or verification, an empty history
   * and a default config.
   */
  public StvsRootModel() {
    hybridSpecifications = new ArrayList<>();
    globalConfig = new GlobalConfig();
    history = new History();
    scenario = new VerificationScenario();
  }

  /**
   * Create a new StvsRootModel from the given hybrid specifications, config, history and code.
   * @param hybridSpecifications
   * @param globalConfig
   * @param history
   * @param code
   */
  public StvsRootModel(List<HybridSpecification> hybridSpecifications, GlobalConfig globalConfig,
                       History history, Code code) {
    this.hybridSpecifications = hybridSpecifications;
    this.globalConfig = globalConfig;
    this.history = history;
    this.scenario = new VerificationScenario(code);
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
