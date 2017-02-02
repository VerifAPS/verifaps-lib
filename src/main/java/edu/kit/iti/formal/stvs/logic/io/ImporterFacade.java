package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.function.Consumer;

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

  public static HybridSpecification importHybridSpec(InputStream input, ImportFormat format) {

    // TODO: implement
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


  /**
   * imports a file with unknown type
   * @param file file to open
   * @param specificationConsumer consumer of the file (if the file is a Specification)
   * @param rootModelConsumer consumer of the file (if the file is a rootModel)
   * @param scenarioConsumer consumer of the file (if the file is a scenario)
   * @throws IOException exception while reading a file
   */
  public static void importFile(File file, Consumer<HybridSpecification>
      specificationConsumer, Consumer<StvsRootModel> rootModelConsumer,
                                Consumer<VerificationScenario> scenarioConsumer) throws
      IOException {
    // TODO: implement
  }

}
