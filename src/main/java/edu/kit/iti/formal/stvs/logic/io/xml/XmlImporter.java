package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.Importer;
import org.apache.commons.io.IOUtils;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;

/**
 * @author Benjamin Alt
 */
public abstract class XmlImporter<T> implements Importer<T> {
  private final String INPUT_ENCODING = "utf8";

  public T doImport(InputStream source) throws ImportException {
    StringWriter writer = new StringWriter();
    try {
      IOUtils.copy(source, writer, INPUT_ENCODING);
      String inputString = writer.toString();
      Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder()
          .parse(new InputSource(new StringReader(inputString)));
      return doImportFromXmlNode(doc.getDocumentElement());
    } catch (SAXException | IOException | ParserConfigurationException e) {
      throw new ImportException(e);
    }
  }

  public abstract T doImportFromXmlNode(Node source);
}
