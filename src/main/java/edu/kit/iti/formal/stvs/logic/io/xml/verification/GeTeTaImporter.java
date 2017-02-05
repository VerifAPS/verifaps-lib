package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1_0.report.Counterexample;
import edu.kit.iti.formal.exteta_1_0.report.Message;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.xml.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlImporter;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.net.URISyntaxException;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporter extends XmlImporter<VerificationResult> {

  private final String RETURN_CODE_SUCCESS = "0"; // TODO: Determine actual

  @Override
  public VerificationResult doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Message importedMessage = ((JAXBElement<Message>) jaxbUnmarshaller.unmarshal(source)).getValue();
      if (importedMessage.getReturncode().equals(RETURN_CODE_SUCCESS)) {
        return new VerificationResult();
      } else {
        return new VerificationResult(parseCounterexample(importedMessage.getCounterexample()));
      }
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  // TODO Implement once I know what a concrete instance of their counterexamples looks like
  private ConcreteSpecification parseCounterexample(Counterexample counterexample) {
    return null;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/report.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}
