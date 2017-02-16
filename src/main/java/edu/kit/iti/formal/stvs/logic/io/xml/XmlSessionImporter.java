package edu.kit.iti.formal.stvs.logic.io.xml;

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
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

/**
 * @author Benjamin Alt
 */
public class XmlSessionImporter extends XmlImporter<StvsRootModel> {

  private XmlConstraintSpecImporter constraintSpecImporter;
  // private XmlConfigImporter configImporter;
  private ObjectFactory objectFactory;
  private GlobalConfig currentConfig;

  public XmlSessionImporter(GlobalConfig currentConfig) throws ImportException {
    constraintSpecImporter = new XmlConstraintSpecImporter();
    //configImporter = new XmlConfigImporter();
    this.objectFactory = new ObjectFactory();
    this.currentConfig = currentConfig;
  }

  @Override
  public StvsRootModel doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Session importedSession = ((JAXBElement<Session>) jaxbUnmarshaller.unmarshal(source))
          .getValue();

      // Code
      Code code = new Code();
      code.updateSourcecode(importedSession.getCode().getPlaintext());
      VerificationScenario scenario = new VerificationScenario(code);

      List<Type> typeContext = Optional.ofNullable(code.getParsedCode())
          .map(ParsedCode::getDefinedTypes)
          .orElse(Arrays.asList(TypeInt.INT, TypeBool.BOOL));

      // Initialized later, since we need to know the types that are available before we import
      XmlConcreteSpecImporter concreteSpecImporter = new XmlConcreteSpecImporter(typeContext);

      /* Config (optional in xsd, not imported/exported with session right now but separately,
      as per customer request)
      GlobalConfig config = new GlobalConfig();
      if (importedSession.getConfig() != null) {
        JAXBElement<Config> element = objectFactory.createConfig(importedSession.getConfig());
        config = configImporter.doImportFromXmlNode(XmlExporter.marshalToNode(element));
      } */

      // History
      History history = new History();
      for (String codeFile : importedSession.getHistory().getCode()) {
        history.addCodeFile(codeFile);
      }
      for (String specFile : importedSession.getHistory().getSpec()) {
        history.addSpecFile(specFile);
      }

      // Tabs
      List<HybridSpecification> hybridSpecs = new ArrayList<>();
      for (Tab tab : importedSession.getTabs().getTab()) {
        HybridSpecification hybridSpec = null;
        ConcreteSpecification counterExample = null;
        ConcreteSpecification concreteInstance = null;
        for (SpecificationTable specTable : tab.getSpecification()) {
          JAXBElement<SpecificationTable> element = objectFactory.createSpecification(specTable);
          if (!specTable.isIsConcrete()) {
            if (hybridSpec != null) {
              throw new ImportException("Tab may not have more than one abstract specification");
            }
            ConstraintSpecification constraintSpec = constraintSpecImporter.doImportFromXmlNode
                (XmlExporter.marshalToNode(element));
            hybridSpec = new HybridSpecification(constraintSpec, !tab.isReadOnly());
          } else {
            ConcreteSpecification concreteSpec = concreteSpecImporter.doImportFromXmlNode
                (XmlExporter.marshalToNode(element));
            if (concreteSpec.isCounterExample()) {
              counterExample = concreteSpec;
            } else {
              concreteInstance = concreteSpec;
            }
          }
        }
        if (hybridSpec == null) {
          throw new ImportException("Tab must have at least one abstract specification");
        }
        hybridSpec.setCounterExample(counterExample);
        hybridSpec.setConcreteInstance(concreteInstance);
        hybridSpecs.add(hybridSpec);
      }

      return new StvsRootModel(hybridSpecs, currentConfig, history, scenario, new File(System
          .getProperty("user.home")), ""); // TODO: better file selection
    } catch (JAXBException | ExportException e) {
      throw new ImportException(e);
    }
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File(this.getClass().getResource("/fileFormats/session.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}
