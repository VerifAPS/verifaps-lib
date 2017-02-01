package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.InputStream;

/**
 * @author Benjamin Alt
 */
public class ImporterFacade {

  public enum ImportFormat {
    XML,
    GETETA
  }

  public static ConstraintSpecification importSpec(InputStream input, ImportFormat format) {
    return null;
  }

  public static GlobalConfig importConfig(InputStream input, ImportFormat format) {
    return null;
  }

  public static StvsRootModel importSession(InputStream input, ImportFormat format) {
    return null;
  }

  public static VerificationScenario importVerificationScenario(InputStream input, ImportFormat format) {
    return null;
  }
}
