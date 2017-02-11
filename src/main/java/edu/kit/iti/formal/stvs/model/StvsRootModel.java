package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class StvsRootModel {

  private ObservableList<HybridSpecification> hybridSpecifications;
  private GlobalConfig globalConfig;
  private History history;
  private VerificationScenario scenario;
  private File workingdir;

  /**
   * Create a new empty StvsRootModel with no specifications or verification, an empty history
   * and a default config.
   */
  public StvsRootModel() {
    this(
        FXCollections.observableArrayList(),
        new GlobalConfig(),
        new History(),
        new VerificationScenario(),
        new File(System.getProperty("user.home")));
  }

  /**
   * Create a new StvsRootModel from the given hybrid specifications, config, history and code.
   * @param hybridSpecifications
   * @param globalConfig
   * @param history
   * @param scenario
   * @param workingdir working-directory that should be used (e.g. for opening and saving)
   */
  public StvsRootModel(List<HybridSpecification> hybridSpecifications, GlobalConfig globalConfig,
                       History history, VerificationScenario scenario, File workingdir) {
    this.hybridSpecifications = FXCollections.observableArrayList(hybridSpecifications);
    this.globalConfig = globalConfig;
    this.history = history;
    this.scenario = scenario;
    this.workingdir = workingdir;
  }

  public ObservableList<HybridSpecification> getHybridSpecifications() {
    return hybridSpecifications;
  }

  public GlobalConfig getGlobalConfig() {
    return globalConfig;
  }

  public void setGlobalConfig(GlobalConfig globalConfig) {
    this.globalConfig = globalConfig;
  }

  public History getHistory() {
    return history;
  }

  public VerificationScenario getScenario() {
    return scenario;
  }

  public void setScenario(VerificationScenario verificationScenario) {
    // TODO: implement event passing etc.
    this.scenario = verificationScenario;
  }

  public File getWorkingdir() {
    return workingdir;
  }

  public void setWorkingdir(File workingdir) {
    this.workingdir = workingdir;
  }


}
