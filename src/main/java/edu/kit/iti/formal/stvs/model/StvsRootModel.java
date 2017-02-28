package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.File;
import java.io.IOException;
import java.util.List;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * @author Benjamin Alt
 */
public class StvsRootModel {

  private static final String AUTOLOAD_SESSION_FILENAME = "stvs-session.xml";

  private ObservableList<HybridSpecification> hybridSpecifications;
  private GlobalConfig globalConfig;
  private History history;
  private VerificationScenario scenario;
  private File workingdir;

  private String filename;

  /**
   * Create a new empty StvsRootModel with no specifications or verification, an empty history and a
   * default config.
   */
  public StvsRootModel() {
    this(FXCollections.observableArrayList(), new GlobalConfig(), new History(),
        new VerificationScenario(), new File(System.getProperty("user.home")), "");
  }

  /**
   * Create a new StvsRootModel from the given hybrid specifications, config, history and code.
   *
   * @param hybridSpecifications
   * @param globalConfig
   * @param history
   * @param scenario
   * @param workingdir working-directory that should be used (e.g. for opening and saving)
   * @param filename filename of stvsrootmodel
   */
  public StvsRootModel(List<HybridSpecification> hybridSpecifications, GlobalConfig globalConfig,
      History history, VerificationScenario scenario, File workingdir, String filename) {
    this.hybridSpecifications = FXCollections.observableArrayList(hybridSpecifications);
    this.globalConfig = globalConfig;
    this.history = history;
    this.scenario = scenario;
    this.workingdir = workingdir;
    this.filename = filename;
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
    this.scenario = verificationScenario;
  }

  public File getWorkingdir() {
    return workingdir;
  }

  public void setWorkingdir(File workingdir) {
    this.workingdir = workingdir;
  }

  public String getFilename() {
    return filename;
  }

  public void setFilename(String filename) {
    this.filename = filename;
  }

  public static StvsRootModel autoloadSession() {
    File sessionFile =
        new File(GlobalConfig.CONFIG_DIRPATH + File.separator + AUTOLOAD_SESSION_FILENAME);
    try {
      return ImporterFacade.importSession(sessionFile, ImporterFacade.ImportFormat.XML,
          new GlobalConfig(), new History());
    } catch (Exception e) {
      return new StvsRootModel();
    }
  }

  public void autosaveSession() throws IOException, ExportException {
    File configDir = new File(GlobalConfig.CONFIG_DIRPATH);
    if (!configDir.isDirectory() || !configDir.exists()) {
      configDir.mkdirs();
    }
    File sessionFile =
        new File(GlobalConfig.CONFIG_DIRPATH + File.separator + AUTOLOAD_SESSION_FILENAME);
    ExporterFacade.exportSession(this, ExporterFacade.ExportFormat.XML, sessionFile);
  }

}
