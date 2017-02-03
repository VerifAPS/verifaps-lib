package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario;
import org.w3c.dom.Node;

import java.io.File;
import java.net.URISyntaxException;

/**
 * @author Benjamin Alt
 * TODO: Do we change VerificationScenario?
 */
public class XmlVerificationScenarioImporter extends XmlImporter<VerificationScenario> {

  @Override
  public VerificationScenario doImportFromXmlNode(Node source) throws ImportException {

    /*
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
       importedSession = ((JAXBElement<Session>) jaxbUnmarshaller.unmarshal(source))
          .getValue();
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
    *
    */
    return null;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File(this.getClass().getResource("/fileFormats/verification_scenario.xsd")
        .toURI());
    return xsdFile.getAbsolutePath();
  }
}
