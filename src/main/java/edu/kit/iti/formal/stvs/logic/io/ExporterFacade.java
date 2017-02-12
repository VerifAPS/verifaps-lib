package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaExporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import org.antlr.v4.runtime.Token;

import java.io.*;
import java.util.List;

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
        return new XmlConstraintSpecExporter().export(spec);
      case GETETA:
        return new GeTeTaExporter().export(spec);
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

  /**
   * exports code to the file specified in code-model
   * @param code Code to export
   * @throws IOException will be thrown, when an error occurs while saving
   */
  public static void exportCode(Code code, boolean escapeVariables) throws IOException {
    exportCode(code, new File(code.getFilename()), escapeVariables);
  }

  public static void exportCode(Code code, File file, boolean escapeVariables) throws IOException {
    BufferedWriter writer = new BufferedWriter(new FileWriter(file));
    if (escapeVariables) writer.write(VariableEscaper.escapeCode(code));
    else writer.write(code.getSourcecode());
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
