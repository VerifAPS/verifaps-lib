package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.logic.io.xml.*;
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
import org.apache.commons.io.IOUtils;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
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

/**
 * @author Benjamin Alt
 */
public class ImporterFacade {

  public enum ImportFormat {
    XML,
    GETETA
  }

  public static ConstraintSpecification importConstraintSpec(InputStream input, ImportFormat
      format) throws ImportException {
    switch (format) {
      case XML:
        return new XmlConstraintSpecImporter().doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static ConstraintSpecification importConstraintSpec(File file, ImportFormat format) throws
      IOException, ImportException {
    return importConstraintSpec(new FileInputStream(file), format);
  }

  public static ConcreteSpecification importConcreteSpec(InputStream input, ImportFormat format,
                                                         List<Type> typeContext) throws ImportException {
    switch (format) {
      case XML:
        return new XmlConcreteSpecImporter(typeContext).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static ConcreteSpecification importConcreteSpec(File file, ImportFormat format,
                                                         List<Type> typeContext) throws
      IOException, ImportException {
    return importConcreteSpec(new FileInputStream(file), format, typeContext);
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

  public static StvsRootModel importSession(InputStream input, ImportFormat format, GlobalConfig
      currentConfig, History currentHistory) throws ImportException {
    switch (format) {
      case XML:
        return new XmlSessionImporter(currentConfig, currentHistory).doImport(input);
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  public static StvsRootModel importSession(File file, ImportFormat format, GlobalConfig
      currentConfig, History currentHistory)
      throws
      IOException,
      ImportException {
    return importSession(new FileInputStream(file), format, currentConfig, currentHistory);
  }

  public static Code importStCode(File chosenFile) throws IOException {
    String plaintext = new String(Files.readAllBytes(Paths.get(chosenFile.getAbsolutePath())));
    return new Code(chosenFile.getAbsolutePath(), plaintext);
  }

  public static History importHistory(File chosenFile, ImportFormat format) throws JAXBException, ImportException {
    switch (format) {
      case XML:
        JAXBContext context = JAXBContext.newInstance("edu.kit.iti.formal.stvs.logic.io.xml");
        JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.History> element =
            (JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.History>) context.createUnmarshaller()
                .unmarshal(chosenFile);
        return new History(element.getValue().getFilename());
      default:
        throw new ImportException("Unsupported import format");
    }
  }

  /**
   * imports a file with unknown type
   *
   * @param file                  file to open
   * @param globalConfig          current global config
   * @param importHybridSpecificationHandler consumer of the file (if the file is a Specification)
   * @param importStvsRootModelHandler     consumer of the file (if the file is a Session)
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
      Document doc = dbf.newDocumentBuilder()
          .parse(new InputSource(new StringReader(inputString)));
      if (doc != null && doc.getFirstChild() != null) {
        Node rootNode = doc.getFirstChild();
        switch (rootNode.getNodeName()) {
          case "session":
            importStvsRootModelHandler.accept(importSession(file, ImportFormat.XML, globalConfig,
                currentHistory));
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
      //ignore, because it might have been code
    }
    codeConsumer.accept(importStCode(file));
  }

}
