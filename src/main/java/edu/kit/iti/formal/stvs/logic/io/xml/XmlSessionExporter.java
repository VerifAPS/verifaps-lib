package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.math.BigInteger;

/**
 * @author Benjamin Alt
 */
public class XmlSessionExporter extends XmlExporter<StvsRootModel> {
  private XmlConfigExporter configExporter;
  private XmlSpecExporter specExporter;
  private ObjectFactory objectFactory;

  public XmlSessionExporter() {
    configExporter = new XmlConfigExporter();
    specExporter = new XmlSpecExporter();
    objectFactory = new ObjectFactory();
  }

  @Override
  public Node exportToXmlNode(StvsRootModel source) throws ExportException {
    try {
      Session session = objectFactory.createSession();

      // Code
      Code code = objectFactory.createCode();
      code.setPlaintext(source.getScenario().getCode().getSourcecode());
      session.setCode(code);

      // Config
      Node configNode = configExporter.exportToXmlNode(source.getGlobalConfig());
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Config importedConfig = ((JAXBElement<Config>) jaxbUnmarshaller.unmarshal(configNode))
          .getValue();
      session.setConfig(importedConfig);

      //History
      session.setHistory(makeHistory(source));

      // Tabs
      session.setTabs(makeTabs(source));
      JAXBElement<Session> element = objectFactory.createSession(session);
      return marshalToNode(element);
    } catch (JAXBException e) {
      throw new ExportException(e);
    }
  }

  private History makeHistory(StvsRootModel source) {
    History exportedHistory = objectFactory.createHistory();
    for (String codeFile : source.getHistory().getCodeFiles()) {
      exportedHistory.getCode().add(codeFile);
    }
    for (String specFile : source.getHistory().getSpecFiles()) {
      exportedHistory.getSpec().add(specFile);
    }
    return exportedHistory;
  }

  private Session.Tabs makeTabs(StvsRootModel source) throws ExportException {
    try {
      Session.Tabs tabs = objectFactory.createSessionTabs();
      for (int i = 0; i < source.getHybridSpecifications().size(); i++) {
        HybridSpecification hybridSpec = source.getHybridSpecifications().get(i);
        // One tab corresponds to one HybridSpecification
        Tab tab = objectFactory.createTab();
        tab.setId(BigInteger.valueOf(i));
        tab.setReadOnly(!hybridSpec.isEditable());
        tab.setOpen(false); // TODO: Should we delete this from XSD?
        Node constraintSpecNode = specExporter.exportToXmlNode(hybridSpec);
        JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
        Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        SpecificationTable constraintSpec = ((JAXBElement<SpecificationTable>) jaxbUnmarshaller
            .unmarshal(constraintSpecNode)).getValue();
        tab.getSpecification().add(constraintSpec);
        if (hybridSpec.getConcreteInstance() != null) {
          Node concreteSpecNode = specExporter.exportToXmlNode(hybridSpec.getConcreteInstance());
          SpecificationTable concreteSpec = ((JAXBElement<SpecificationTable>) jaxbUnmarshaller
              .unmarshal(concreteSpecNode)).getValue();
          tab.getSpecification().add(concreteSpec);
        }
        tabs.getTab().add(tab);
      }
      return tabs;
    } catch (JAXBException e) {
      throw new ExportException(e);
    }
  }
}
