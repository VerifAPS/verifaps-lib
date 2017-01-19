package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.Importer;
import org.w3c.dom.Node;

/**
 * Created by bal on 11.01.17.
 */
public abstract class XmlImporter<T> implements Importer<T> {
  public Node readFromFile(String xmlFilename) {
    return null;
  }

  public T doImportFromXmlNode(Node node) {
    return null;
  }
}
