package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.logic.io.xml.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaExporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;

/**
 * Facade class for facilitating the export of different objects to different export formats.
 *
 * @author Benjamin Alt
 */
public class ExporterFacade {

  /**
   * Exports a {@link ConstraintSpecification} using the specified {@link ExportFormat}.
   *
   * @param spec The specification that should be exported
   * @param format The format for exporting
   * @return The stream the exported object is written to
   * @throws ExportException if an error occurred while exporting
   */
  public static ByteArrayOutputStream exportSpec(ConstraintSpecification spec, ExportFormat format)
      throws ExportException {
    switch (format) {
      case XML:
        return new XmlConstraintSpecExporter().export(spec);
      case GETETA:
        return new GeTeTaExporter().export(spec);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * Exports a {@link ConstraintSpecification} to a given file.
   *
   * @param spec The spec to export
   * @param format The format to use
   * @param file The file to write to
   * @throws IOException if an error occurred while saving
   * @throws ExportException if an error occurred while exporting
   */
  public static void exportSpec(ConstraintSpecification spec, ExportFormat format, File file)
      throws IOException, ExportException {
    writeToFile(exportSpec(spec, format), file);
  }

  /**
   * Exports a {@link GlobalConfig} using the specified {@link ExportFormat}.
   *
   * @param config The configuration that should be exported
   * @param format The format for exporting
   * @return The stream the exported object is written to
   * @throws ExportException if an error occurred while exporting
   */
  public static ByteArrayOutputStream exportConfig(GlobalConfig config, ExportFormat format)
      throws ExportException {
    switch (format) {
      case XML:
        return new XmlConfigExporter().export(config);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * Exports a {@link GlobalConfig} to a given file.
   *
   * @param config The config that should be exported
   * @param format The format to use
   * @param file The file to write to
   * @throws IOException if an error occurred while saving
   * @throws ExportException if an error occurred while exporting
   */
  public static void exportConfig(GlobalConfig config, ExportFormat format, File file)
      throws IOException, ExportException {
    writeToFile(exportConfig(config, format), file);
  }

  /**
   * Exports a {@link StvsRootModel} using the specified {@link ExportFormat}.
   *
   * @param session The root model that should be exported
   * @param format The format for exporting
   * @return The stream the exported object is written to
   * @throws ExportException if an error occurred while exporting
   */
  public static ByteArrayOutputStream exportSession(StvsRootModel session, ExportFormat format)
      throws ExportException {
    switch (format) {
      case XML:
        return new XmlSessionExporter().export(session);
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * Exports a {@link StvsRootModel} to a given file.
   *
   * @param session The session that should be exported
   * @param format The format to use
   * @param file The file to write to
   * @throws IOException if an error occurred while saving
   * @throws ExportException if an error occurred while exporting
   */
  public static void exportSession(StvsRootModel session, ExportFormat format, File file)
      throws IOException, ExportException {
    writeToFile(exportSession(session, format), file);
  }

  /**
   * Exports a {@link Code} to the file specified in {@link Code#filename}.
   *
   * @param code The code to export
   * @param escapeVariables Specifies if variables should be escaped
   * @throws IOException if an error occurs while saving
   */
  public static void exportCode(Code code, boolean escapeVariables) throws IOException {
    exportCode(code, new File(code.getFilename()), escapeVariables);
  }

  /**
   * Exports a {@link Code} to a given file.
   *
   * @param code The code that should be exported
   * @param file The file to write to
   * @param escapeVariables Specifies if variables should be escaped
   * @throws IOException if an error occurs while saving
   */
  public static void exportCode(Code code, File file, boolean escapeVariables) throws IOException {
    BufferedWriter writer = new BufferedWriter(
        new OutputStreamWriter(new FileOutputStream(file), StandardCharsets.UTF_8));
    if (escapeVariables) {
      writer.write(VariableEscaper.escapeCode(code));
    } else {
      writer.write(code.getSourcecode());
    }
    writer.close();
  }

  /**
   * Exports a {@link History} to a file.
   *
   * @param history The history to export
   * @param format The format to use
   * @param file The file to write ro
   * @throws IOException if an error occurred while saving
   * @throws ExportException if an error occurred while exporting
   * @throws JAXBException if an error occurred while marshalling
   */
  public static void exportHistory(History history, ExportFormat format, File file)
      throws ExportException, JAXBException, IOException {
    switch (format) {
      case XML:
        edu.kit.iti.formal.stvs.logic.io.xml.History exportHistory =
            new ObjectFactory().createHistory();
        for (String filename : history.getFilenames()) {
          exportHistory.getFilename().add(filename);
        }
        ByteArrayOutputStream bos = new ByteArrayOutputStream();
        JAXBContext context = JAXBContext.newInstance(XmlExporter.NAMESPACE);
        JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.History> element =
            new ObjectFactory().createHistory(exportHistory);
        context.createMarshaller().marshal(element, bos);
        writeToFile(bos, file);
        break;
      default:
        throw new ExportException("Unsupported export format");
    }
  }

  /**
   * Write an OutputStream to a file.
   *
   * @param outputStream The stream to write to a file
   * @param file The file to write to
   * @throws IOException if an error occurred during file I/O
   */
  private static void writeToFile(ByteArrayOutputStream outputStream, File file)
      throws IOException {
    FileOutputStream fostream = null;
    try {
      fostream = new FileOutputStream(file);
      outputStream.writeTo(fostream);
      fostream.close();
    } finally { // Ensure that the outputstream is always closed
      if (fostream != null) {
        fostream.close();
      }
    }
  }

  public enum ExportFormat {
    XML, GETETA
  }
}
