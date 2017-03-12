package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;

import java.math.BigInteger;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.w3c.dom.Node;

/**
 * This class provides the functionality to export whole sessions, code and all specification tabs,
 * to xml. {@link XmlConstraintSpecExporter} and {@link XmlConcreteSpecExporter} are used to export
 * the specifications.
 *
 * @author Benjamin Alt
 */
public class XmlSessionExporter extends XmlExporter<StvsRootModel> {
  // private XmlConfigExporter configExporter;
  private XmlConstraintSpecExporter constraintSpecExporter;
  private XmlConcreteSpecExporter concreteSpecExporter;
  private ObjectFactory objectFactory;

  /**
   * Creates an exporter.
   */
  public XmlSessionExporter() {
    // configExporter = new XmlConfigExporter();
    constraintSpecExporter = new XmlConstraintSpecExporter();
    concreteSpecExporter = new XmlConcreteSpecExporter();
    objectFactory = new ObjectFactory();
  }

  /**
   * Exports a {@link StvsRootModel} to xml.
   *
   * @param source Model that should be converted
   * @return Xml representing the session
   * @throws ExportException Exception while exporting
   */
  @Override
  public Node exportToXmlNode(StvsRootModel source) throws ExportException {
    Session session = objectFactory.createSession();

    // Code
    Code code = objectFactory.createCode();
    code.setPlaintext(source.getScenario().getCode().getSourcecode());
    session.setCode(code);

    // Tabs
    session.setTabs(makeTabs(source));
    JAXBElement<Session> element = objectFactory.createSession(session);
    return marshalToNode(element, NAMESPACE);
  }

  /**
   * Extracts the tabs from the {@link StvsRootModel} and converts them into {@link Session.Tabs}.
   *
   * @param source model to export the tabs from
   * @return exported tabs
   * @throws ExportException exception while exporting
   */
  private Session.Tabs makeTabs(StvsRootModel source) throws ExportException {
    try {
      Session.Tabs tabs = objectFactory.createSessionTabs();
      for (int i = 0; i < source.getHybridSpecifications().size(); i++) {
        HybridSpecification hybridSpec = source.getHybridSpecifications().get(i);
        // One tab corresponds to one HybridSpecification
        Tab tab = objectFactory.createTab();
        tab.setId(BigInteger.valueOf(i));
        tab.setReadOnly(!hybridSpec.isEditable());
        tab.setOpen(false);
        Node constraintSpecNode = constraintSpecExporter.exportToXmlNode(hybridSpec);
        JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
        Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
        SpecificationTable constraintSpec =
            ((JAXBElement<SpecificationTable>) jaxbUnmarshaller.unmarshal(constraintSpecNode))
                .getValue();
        tab.getSpecification().add(constraintSpec);

        ConcreteSpecification concreteSpecification = null;
        if (hybridSpec.getConcreteInstance().isPresent()) {
          concreteSpecification = hybridSpec.getConcreteInstance().get();
        } else if (hybridSpec.getCounterExample().isPresent()) {
          concreteSpecification = hybridSpec.getCounterExample().get();
        }
        if (concreteSpecification != null) {
          Node concreteSpecNode = concreteSpecExporter.exportToXmlNode(concreteSpecification);
          SpecificationTable concreteSpec =
              ((JAXBElement<SpecificationTable>) jaxbUnmarshaller.unmarshal(concreteSpecNode))
                  .getValue();
          tab.getSpecification().add(concreteSpec);
        }

        tabs.getTab().add(tab);
      }
      return tabs;
    } catch (JAXBException exception) {
      throw new ExportException(exception);
    }
  }
}
