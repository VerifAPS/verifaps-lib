package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.Importer;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlImporter;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import org.w3c.dom.Node;

import java.io.File;
import java.io.InputStream;
import java.net.URISyntaxException;

/**
 * @author Benjamin Alt
 */
public class VerificationImporter extends XmlImporter<VerificationResult> {

  @Override
  public VerificationResult doImport(InputStream source) throws ImportException {
    return null;
  }

  @Override
  public VerificationResult doImportFromXmlNode(Node source) throws ImportException {
    return null;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/report.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}
