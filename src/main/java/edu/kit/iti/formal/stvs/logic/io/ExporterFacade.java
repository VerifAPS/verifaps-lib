package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;

/**
 * Facade class for facilitating the export of different objects to different export formats.
 * @author Benjamin Alt
 */
public class ExporterFacade {

  public enum ExportFormat {
    XML,
    GETETA
  }

  public static OutputStream exportSpec(ConstraintSpecification spec, ExportFormat format) {
    return null;
  }

  /**
   * exports spec to a given file
   * @param spec spec to export
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportSpec(ConstraintSpecification spec, ExportFormat format, File file)
      throws IOException {

  }

  public static OutputStream exportConfig(GlobalConfig config, ExportFormat format) {
    return null;
  }

  /**
   * exports config to a given file
   * @param config config that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportConfig(GlobalConfig config, ExportFormat format, File file) throws
      IOException {

  }

  public static OutputStream exportSession(StvsRootModel session, ExportFormat format) {
    return null;
  }

  /**
   * exports session to a given file
   * @param session session that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportSession(StvsRootModel session, ExportFormat format, File file) throws
      IOException {

  }

  public static OutputStream exportVerificationScenario(VerificationScenario scenario,
                                                ExportFormat format) {
    return null;
  }

  /**
   * exports verificationscenario to a given file
   * @param verificationScenario verification scenario that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportVerificationScenario(VerificationScenario verificationScenario,
                                                ExportFormat format, File file) throws IOException {

  }
}
