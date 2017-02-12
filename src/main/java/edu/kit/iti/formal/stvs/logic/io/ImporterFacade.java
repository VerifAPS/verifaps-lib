package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.function.Consumer;

/**
 * @author Benjamin Alt
 */
public class ImporterFacade {

  public enum ImportFormat {
    XML,
    GETETA
  }

  public static ConstraintSpecification importSpec(InputStream input, ImportFormat format) throws ImportException {
    switch (format) {
      case XML:
        return new XmlConstraintSpecImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static ConstraintSpecification importSpec(File file, ImportFormat format) throws
      IOException, ImportException {
    return importSpec(new FileInputStream(file), format);
  }

  public static HybridSpecification importHybridSpec(InputStream input, ImportFormat format) throws ImportException {
    switch (format) {
      case XML:
        ConstraintSpecification constraintSpec = new XmlConstraintSpecImporter().doImport(input);
        return new HybridSpecification(constraintSpec, true);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static HybridSpecification importHybridSpec(File file, ImportFormat format) throws
      IOException, ImportException {
    return importHybridSpec(new FileInputStream(file), format);
  }

  public static GlobalConfig importConfig(InputStream input, ImportFormat format) throws ImportException {
    switch (format) {
      case XML:
        return new XmlConfigImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static VerificationResult importVerificationResult(InputStream input, ImportFormat
      format, List<Type> typeContext) throws ImportException {
    switch (format) {
      case GETETA:
        return new GeTeTaImporter(typeContext).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static GlobalConfig importConfig(File file, ImportFormat format) throws FileNotFoundException, ImportException {
    return importConfig(new FileInputStream(file), format);
  }

  public static StvsRootModel importSession(InputStream input, ImportFormat format) throws ImportException {
    switch (format) {
      case XML:
        return new XmlSessionImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static StvsRootModel importSession(File file, ImportFormat format) throws IOException, ImportException {
    return importSession(new FileInputStream(file), format);
  }

  public static Code importStCode(File chosenFile) throws IOException {
    String plaintext = new String(Files.readAllBytes(Paths.get(chosenFile.getAbsolutePath())));
    return new Code(chosenFile.getAbsolutePath(), plaintext);
  }


  /**
   * imports a file with unknown type
   *
   * @param file                  file to open
   * @param specificationConsumer consumer of the file (if the file is a Specification)
   * @param rootModelConsumer     consumer of the file (if the file is a rootModel)
   * @param scenarioConsumer      consumer of the file (if the file is a scenario)
   * @throws IOException exception while reading a file
   */
  public static void importFile(File file, Consumer<HybridSpecification>
      specificationConsumer, Consumer<StvsRootModel> rootModelConsumer,
                                Consumer<VerificationScenario> scenarioConsumer) throws
      IOException {
    // TODO: implement
  }

}
