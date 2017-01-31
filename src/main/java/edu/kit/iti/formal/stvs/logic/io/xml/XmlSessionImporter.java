package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import org.w3c.dom.Node;

import java.io.InputStream;
import java.net.URISyntaxException;

/**
 * Created by bal on 11.01.17.
 */
public class XmlSessionImporter extends XmlImporter<StvsRootModel> {
  @Override
  public StvsRootModel doImportFromXmlNode(Node source) {
    return null;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    return null;
  }
}
