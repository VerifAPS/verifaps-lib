package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import org.w3c.dom.Node;

/**
 * @author Benjamin Alt
 */
public class XmlSessionImporter extends XmlImporter<StvsRootModel> {

  private XmlSpecImporter specImporter;
  private XmlConfigImporter configImporter;
  private ObjectFactory objectFactory;

  public XmlSessionImporter() throws ImportException {
    specImporter = new XmlSpecImporter();
    configImporter = new XmlConfigImporter();
    objectFactory = new ObjectFactory();

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

      // Config
      GlobalConfig config = new GlobalConfig();
      if (importedSession.getConfig() != null) {
        JAXBElement<Config> element = objectFactory.createConfig(importedSession.getConfig());
        config = configImporter.doImportFromXmlNode(XmlExporter.marshalToNode(element));
      }

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
        // Each tab corresponds to a hybridSpecification
        HybridSpecification hybridSpec = new HybridSpecification(new HashSet<>(),
            new HashSet<CodeIoVariable>(), new FreeVariableSet(), !tab.isReadOnly());
        for (SpecificationTable specTable : tab.getSpecification()) {
          boolean hasAbstract = false;
          JAXBElement<SpecificationTable> element = objectFactory.createSpecification(specTable);
          if (!specTable.isIsConcrete()) {
            ConstraintSpecification constraintSpec = specImporter.doImportFromXmlNode
                (XmlExporter.marshalToNode(element));
            hybridSpec.getColumns().addAll(constraintSpec.getColumns());
            hybridSpec.getTypeContext().addAll(constraintSpec.getTypeContext());
            hybridSpec.getCodeIoVariables().addAll(constraintSpec.getCodeIoVariables());
            hybridSpec.getFreeVariableSet().getVariableSet().addAll(constraintSpec
                .getFreeVariableSet().getVariableSet());
            hasAbstract = true;
          } else {
            ConcreteSpecification concreteSpec = specImporter.doImportConcreteFromXmlNode
                (XmlExporter.marshalToNode(element));
            if (concreteSpec.isCounterExample()) {
              hybridSpec.setCounterExample(concreteSpec);
            } else {
              hybridSpec.setConcreteInstance(concreteSpec);
            }
          }
          if (!hasAbstract) {
            throw new ImportException("Tab must have at least one abstract specification");
          }
        }
        hybridSpecs.add(hybridSpec);
      }

      return new StvsRootModel(hybridSpecs, config, history, scenario, new File(System
          .getProperty("user.home")));
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
