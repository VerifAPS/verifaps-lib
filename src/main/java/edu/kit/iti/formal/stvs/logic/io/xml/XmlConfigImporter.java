package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.w3c.dom.Node;

import java.io.InputStream;

/**
 * @author Benjamin Alt
 */
public class XmlConfigImporter extends XmlImporter<GlobalConfig> {
  @Override
  public GlobalConfig doImportFromXmlNode(Node source) {
    return null;
  }
}
