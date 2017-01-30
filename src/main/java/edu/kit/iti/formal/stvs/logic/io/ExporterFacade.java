package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

/**
 * Facade class for facilitating the export of different objects to different export formats.
 * @author Benjamin Alt
 */
public class ExporterFacade {

  public enum ExportFormat {
    XML,
    GETETA
  }

  public static void exportSpec(ConstraintSpecification spec, ExportFormat format) {

  }

  public static void exportConfig(GlobalConfig config, ExportFormat format) {

  }

  public static void exportSession(StvsRootModel session, ExportFormat format) {

  }

  public static void exportVerificationScenario(VerificationScenario scenario,
                                                ExportFormat format) {

  }
}
