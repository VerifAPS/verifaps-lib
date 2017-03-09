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
 * The model equivalent of a "session". Contains a list of {@link HybridSpecification}s, a
 * {@link GlobalConfig}, a {@link History} and a {@link VerificationScenario} which has a
 * reference to the currently loaded code.
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
   * Create a new empty StvsRootModel with no specifications or code, an empty history and a
   * default config.
   */
  public StvsRootModel() {
    this(FXCollections.observableArrayList(), new GlobalConfig(), new History(),
        new VerificationScenario(), new File(System.getProperty("user.home")), "");
  }

  /**
   * Create a new StvsRootModel from the given {@link HybridSpecification}s, {@link GlobalConfig},
   * {@link History}, {@link VerificationScenario}, working directory and current filename.
   *
   * @param hybridSpecifications The list of {@link HybridSpecification}s.
   * @param globalConfig The global configuration
   * @param history The current history
   * @param scenario The verification scenario (containing a reference to the current code)
   * @param workingdir working-directory that should be used (e.g. for opening and saving)
   * @param filename The filename of the session file. This can be used e.g. for a "Save Session"
   *                 file dialog or other applications when it may be useful to know where a
   *                 session was loaded from, or where it ought to be stored
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

  /**
   * Loads the last session saved via {@link StvsRootModel#autosaveSession()} (see
   * {@link GlobalConfig#CONFIG_DIRPATH} and {@link StvsRootModel#AUTOLOAD_SESSION_FILENAME}.
   * @return The autoloaded root model.
   */
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

  /**
   * Saves the current session to {@link StvsRootModel#AUTOLOAD_SESSION_FILENAME} in the
   * directory {@link GlobalConfig#CONFIG_DIRPATH}.
   * @throws IOException when the directory does not exist and cannot be created
   * @throws ExportException when there is an error during export
   */
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
