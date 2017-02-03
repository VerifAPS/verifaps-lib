package edu.kit.iti.formal.stvs.logic.io;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;
import edu.kit.iti.formal.stvs.logic.io.verification.VerificationExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSpecExporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.*;

/**
 * Facade class for facilitating the export of different objects to different export formats.
 * @author Benjamin Alt
 */
public class ExporterFacade {

  public enum ExportFormat {
    XML,
    GETETA
  }

  public static ByteArrayOutputStream exportSpec(ConstraintSpecification spec, ExportFormat format) throws ExportException {
    switch(format) {
      case XML:
        return new XmlSpecExporter().export(spec);
      case GETETA:
        return new VerificationExporter().export(spec);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * exports spec to a given file
   * @param spec spec to export
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportSpec(ConstraintSpecification spec, ExportFormat format, File file)
      throws IOException, ExportException {
    writeToFile(exportSpec(spec, format), file);
  }

  public static ByteArrayOutputStream exportConfig(GlobalConfig config, ExportFormat format) throws ExportException {
    switch(format) {
      case XML:
        return new XmlConfigExporter().export(config);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * exports config to a given file
   * @param config config that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportConfig(GlobalConfig config, ExportFormat format, File file) throws
      IOException, ExportException {
        writeToFile(exportConfig(config, format), file);
  }

  public static ByteArrayOutputStream exportSession(StvsRootModel session, ExportFormat format) throws ExportException {
    switch(format) {
      case XML:
        return new XmlSessionExporter().export(session);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * exports session to a given file
   * @param session session that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportSession(StvsRootModel session, ExportFormat format, File file) throws
      IOException, ExportException {
    writeToFile(exportSession(session, format), file);
  }

  public static ByteArrayOutputStream exportVerificationScenario(VerificationScenario scenario,
                                                ExportFormat format) throws ExportException {
    switch(format) {
      case XML:
        throw new UnsupportedOperationException("Not yet implemented");
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * exports verificationscenario to a given file
   * @param verificationScenario verification scenario that should be exported
   * @param format format to use (can be found in ExporterFascade.ExportFormat)
   * @param file file to write to
   */
  public static void exportVerificationScenario(VerificationScenario verificationScenario,
                                                ExportFormat format, File file) throws IOException, ExportException {
    writeToFile(exportVerificationScenario(verificationScenario, format), file);
  }

  /**
   * exports code to the file specified in code-model
   * @param code Code to export
   * @throws IOException will be thrown, when an error occurs while saving
   */
  public static void exportCode(Code code) throws IOException {
    File file = new File(code.getFilename());

    BufferedWriter writer = new BufferedWriter(new FileWriter(file));
    writer.write(code.getSourcecode());
    writer.close();
  }

  /**
   * Write an OutputStream to a file.
   * @param outputStream the stream to write to a file
   * @param file the file to write to
   */
  private static void writeToFile(ByteArrayOutputStream outputStream, File file) throws
      IOException {
    FileOutputStream fostream = new FileOutputStream(file);
    outputStream.writeTo(fostream);
  }
}
