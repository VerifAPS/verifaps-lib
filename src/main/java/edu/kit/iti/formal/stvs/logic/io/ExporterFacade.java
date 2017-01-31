package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

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

  public static OutputStream exportConfig(GlobalConfig config, ExportFormat format) {
    return null;
  }

  public static OutputStream exportSession(StvsRootModel session, ExportFormat format) {
    return null;
  }

  public static OutputStream exportVerificationScenario(VerificationScenario scenario,
                                                ExportFormat format) {
    return null;
  }
}
