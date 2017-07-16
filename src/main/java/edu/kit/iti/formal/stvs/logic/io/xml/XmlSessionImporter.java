package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.io._1.*;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.w3c.dom.Node;

/**
 * This class provides the functionality to import whole sessions ({@link StvsRootModel}s) from
 * xml nodes.
 *
 * @author Benjamin Alt
 */
public class XmlSessionImporter extends XmlImporter<StvsRootModel> {

  private XmlConstraintSpecImporter constraintSpecImporter;
  // private XmlConfigImporter configImporter;
  private ObjectFactory objectFactory;
  private GlobalConfig currentConfig;
  private History currentHistory;

  /**
   * Creates an Importer. {@code currentConfig} and {@code currentHistory} are later passed to the
   * new {@link StvsRootModel}.
   *
   * @param currentConfig currently used configuration
   * @param currentHistory currently used history
   * @throws ImportException Exception while importing
   */
  public XmlSessionImporter(GlobalConfig currentConfig, History currentHistory)
      throws ImportException {
    constraintSpecImporter = new XmlConstraintSpecImporter();
    // configImporter = new XmlConfigImporter();
    this.objectFactory = new ObjectFactory();
    this.currentConfig = currentConfig;
    this.currentHistory = currentHistory;
  }

  /**
   * Imports a {@link StvsRootModel} from {@code source}.
   *
   * @param source Node to import
   * @return imported model
   * @throws ImportException Exception while importing.
   */
  @Override
  public StvsRootModel doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Session importedSession =
          ((JAXBElement<Session>) jaxbUnmarshaller.unmarshal(source)).getValue();

      // Code
      Code code = new Code();
      code.updateSourcecode(importedSession.getCode().getPlaintext());
      VerificationScenario scenario = new VerificationScenario(code);

      List<Type> typeContext = Optional.ofNullable(code.getParsedCode())
          .map(ParsedCode::getDefinedTypes).orElse(Arrays.asList(TypeInt.INT, TypeBool.BOOL));

      // Tabs
      List<HybridSpecification> hybridSpecs = importTabs(importedSession, typeContext);

      return new StvsRootModel(hybridSpecs, currentConfig, currentHistory, scenario,
          new File(System.getProperty("user.home")), "");
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Imports tabs from {@link Session}.
   *
   * @param importedSession session from which tabs should be imported
   * @param typeContext type context that should be used for the {@link XmlConcreteSpecImporter}
   * @return list of imported specifications (tabs)
   * @throws ImportException Exception while importing
   */
  private List<HybridSpecification> importTabs(Session importedSession, List<Type> typeContext)
      throws ImportException {
    XmlConcreteSpecImporter concreteSpecImporter = new XmlConcreteSpecImporter(typeContext);
    List<HybridSpecification> hybridSpecs = new ArrayList<>();
    for (Tab tab : importedSession.getTabs().getTab()) {
      HybridSpecification hybridSpec = null;
      ConcreteSpecification counterExample = null;
      ConcreteSpecification concreteInstance = null;
      for (SpecificationTable specTable : tab.getSpecification()) {
        JAXBElement<SpecificationTable> element = objectFactory.createSpecification(specTable);
        try {
          if (!specTable.isIsConcrete()) {
            if (hybridSpec != null) {
              throw new ImportException("Tab may not have more than one abstract specification");
            }
            ConstraintSpecification constraintSpec = constraintSpecImporter.doImportFromXmlNode(
                XmlExporter.marshalToNode(element, XmlExporter.OF_STVS));
            hybridSpec = new HybridSpecification(constraintSpec, !tab.isReadOnly());
          } else {
            ConcreteSpecification concreteSpec = concreteSpecImporter.doImportFromXmlNode(
                XmlExporter.marshalToNode(element, XmlExporter.OF_STVS));
            if (concreteSpec.isCounterExample()) {
              counterExample = concreteSpec;
            } else {
              concreteInstance = concreteSpec;
            }
          }
        } catch (ExportException exception) {
          throw new ImportException(exception);
        }
      }
      if (hybridSpec == null) {
        throw new ImportException("Tab must have at least one abstract specification");
      }
      hybridSpec.setCounterExample(counterExample);
      hybridSpec.setConcreteInstance(concreteInstance);
      hybridSpecs.add(hybridSpec);
    }
    return hybridSpecs;
  }

  @Override
  protected URL getXsdResource() throws IOException {
    return getClass().getResource("/fileFormats/stvs-1.0.xsd");
  }
}
