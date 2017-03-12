package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporter;
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.apache.commons.io.IOUtils;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * Facade class for facilitating the import of different objects from different formats.
 *
 * @author Benjamin Alt
 */
public class ImporterFacade {

  /**
   * Imports a {@link ConstraintSpecification} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which the specification should be imported
   * @param format The format to use for importing
   * @return The imported specification
   * @throws ImportException if an error occurred during importing
   */
  public static ConstraintSpecification importConstraintSpec(InputStream input, ImportFormat format)
      throws ImportException {
    switch (format) {
      case XML:
        return new XmlConstraintSpecImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link ConstraintSpecification} from a file.
   *
   * @param file The file to import from
   * @param format The format to use for importing
   * @return The imported specification
   * @throws IOException if an error occurred while reading the file
   * @throws ImportException if an error occurred while importing
   */
  public static ConstraintSpecification importConstraintSpec(File file, ImportFormat format)
      throws IOException, ImportException {
    return importConstraintSpec(new FileInputStream(file), format);
  }

  /**
   * Imports a {@link ConcreteSpecification} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which to import from
   * @param format The format to use for importing
   * @param typeContext A list of types used in the specification
   * @return The imported specification
   * @throws ImportException if an error occurred during importing
   */
  public static ConcreteSpecification importConcreteSpec(InputStream input, ImportFormat format,
      List<Type> typeContext) throws ImportException {
    switch (format) {
      case XML:
        return new XmlConcreteSpecImporter(typeContext).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link ConcreteSpecification} from a file.
   *
   * @param file The file to import from
   * @param format The format to use for importing
   * @param typeContext A list of types used in the specification
   * @return The imported specification
   * @throws IOException if an error occurred while reading the file
   * @throws ImportException if an error occurred while importing
   */
  public static ConcreteSpecification importConcreteSpec(File file, ImportFormat format,
      List<Type> typeContext) throws IOException, ImportException {
    return importConcreteSpec(new FileInputStream(file), format, typeContext);
  }

  /**
   * Imports a {@link HybridSpecification} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which to import from
   * @param format The format to use for importing
   * @return The imported specification
   * @throws ImportException if an error occurred during importing
   */
  public static HybridSpecification importHybridSpec(InputStream input, ImportFormat format)
      throws ImportException {
    switch (format) {
      case XML:
        ConstraintSpecification constraintSpec = new XmlConstraintSpecImporter().doImport(input);
        return new HybridSpecification(constraintSpec, true);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link HybridSpecification} from a file.
   *
   * @param file The file to import from.
   * @param format The format to use for importing
   * @return The imported specification
   * @throws IOException if an error occured while reading file.
   * @throws ImportException if an error occured while importing.
   */
  public static HybridSpecification importHybridSpec(File file, ImportFormat format)
      throws IOException, ImportException {
    return importHybridSpec(new FileInputStream(file), format);
  }

  /**
   * Imports a {@link GlobalConfig} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which to import from
   * @param format The format to use for importing
   * @return The imported config
   * @throws ImportException exception during importing
   */
  public static GlobalConfig importConfig(InputStream input, ImportFormat format)
      throws ImportException {
    switch (format) {
      case XML:
        return new XmlConfigImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link GlobalConfig} from a file.
   *
   * @param file The file to import from.
   * @param format The format to use for importing
   * @return The imported config
   * @throws FileNotFoundException Exception if file not found.
   * @throws ImportException if an error occured while importing.
   */
  public static GlobalConfig importConfig(File file, ImportFormat format)
      throws FileNotFoundException, ImportException {
    return importConfig(new FileInputStream(file), format);
  }

  /**
   * Imports a {@link VerificationResult} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which to import from
   * @param format The format to use for importing
   * @param typeContext Types in the verified specification
   * @param constraintSpec The constraint specification for which to import a verification result
   * @return The imported result
   * @throws ImportException exception during importing
   */
  public static VerificationResult importVerificationResult(InputStream input, ImportFormat format,
      List<Type> typeContext, ConstraintSpecification constraintSpec) throws ImportException {
    switch (format) {
      case GETETA:
        return new GeTeTaImporter(typeContext, constraintSpec).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link StvsRootModel} from an {@link InputStream} using the specified
   * {@link ImportFormat}.
   *
   * @param input The stream from which to import from
   * @param format The format to use for importing
   * @param currentConfig config to be used for the model
   * @param currentHistory history to be used for the model
   * @return The imported model
   * @throws ImportException exception during importing
   */
  public static StvsRootModel importSession(InputStream input, ImportFormat format,
      GlobalConfig currentConfig, History currentHistory) throws ImportException {
    switch (format) {
      case XML:
        return new XmlSessionImporter(currentConfig, currentHistory).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a {@link StvsRootModel} from a file.
   *
   * @param file The file to import from.
   * @param format The format to use for importing
   * @param currentConfig config to be used for the model
   * @param currentHistory history to be used for the model
   * @return The imported model
   * @throws IOException if an error occured while reading the file
   * @throws ImportException if an error occured while importing
   */
  public static StvsRootModel importSession(File file, ImportFormat format,
      GlobalConfig currentConfig, History currentHistory) throws IOException, ImportException {
    return importSession(new FileInputStream(file), format, currentConfig, currentHistory);
  }

  /**
   * Imports a {@link Code} from a file.
   *
   * @param chosenFile file to import from.
   * @return The imported code
   * @throws IOException if an error occured while reading the file
   */
  public static Code importStCode(File chosenFile) throws IOException {
    String plaintext = new String(Files.readAllBytes(Paths.get(chosenFile.getAbsolutePath())),
        "utf-8");
    return new Code(chosenFile.getAbsolutePath(), plaintext);
  }

  /**
   * Imports a {@link History} from a file.
   *
   * @param chosenFile The file to import from
   * @param format The format to use for importing
   * @return The imported history
   * @throws JAXBException if an error occured while unmarshalling
   * @throws ImportException if an error occured while importing
   */
  public static History importHistory(File chosenFile, ImportFormat format)
      throws JAXBException, ImportException {
    switch (format) {
      case XML:
        JAXBContext context = JAXBContext.newInstance(XmlExporter.NAMESPACE);
        JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.History> element =
            (JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.History>) context.createUnmarshaller()
                .unmarshal(chosenFile);
        return new History(element.getValue().getFilename());
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * Imports a file of unknown type.
   *
   * @param file The file to open
   * @param globalConfig The current global config
   * @param currentHistory history of the opened files to this point
   * @param importHybridSpecificationHandler A file handler (invoked if the file is a Specification)
   * @param importStvsRootModelHandler A file handler (invoked if the file is a Session)
   * @param codeConsumer A file handler (invoked if the file is a code file)
   * @throws IOException general io exception
   * @throws ImportException general importing exception
   */
  public static void importFile(File file, GlobalConfig globalConfig, History currentHistory,
      ImportHybridSpecificationHandler importHybridSpecificationHandler,
      ImportStvsRootModelHandler importStvsRootModelHandler, ImportCodeHandler codeConsumer)
      throws IOException, ImportException {
    StringWriter writer = new StringWriter();
    byte[] byteArray = IOUtils.toByteArray(new FileInputStream(file));
    IOUtils.copy(new ByteArrayInputStream(byteArray), writer, "utf8");
    String inputString = writer.toString();
    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
    dbf.setNamespaceAware(true);
    try {
      Document doc = dbf.newDocumentBuilder().parse(new InputSource(new StringReader(inputString)));
      if (doc != null && doc.getFirstChild() != null) {
        Node rootNode = doc.getFirstChild();
        switch (rootNode.getNodeName()) {
          case "session":
            importStvsRootModelHandler
                .accept(importSession(file, ImportFormat.XML, globalConfig, currentHistory));
            return;
          case "specification":
            importHybridSpecificationHandler.accept(importHybridSpec(file, ImportFormat.XML));
            return;
          default:
            codeConsumer.accept(importStCode(file));
            return;
        }
      }
    } catch (SAXException | ParserConfigurationException | ImportException e) {
      // ignore, because it might have been code
    }
    codeConsumer.accept(importStCode(file));
  }

  public enum ImportFormat {
    XML, GETETA
  }
}
