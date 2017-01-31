package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.Importer;
import org.apache.commons.io.IOUtils;
import org.apache.commons.io.input.CloseShieldInputStream;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import java.io.*;
import java.net.URISyntaxException;

/**
 * @author Benjamin Alt
 */
public abstract class XmlImporter<T> implements Importer<T> {
  private final String INPUT_ENCODING = "utf8";

  private void validateAgainstXSD(InputStream xml) throws SAXException, IOException, URISyntaxException {
    SchemaFactory factory =
        SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
    Schema schema = factory.newSchema(new File(getXSDFilePath()));
    Validator validator = schema.newValidator();
    validator.validate(new StreamSource(xml));
  }

  public T doImport(InputStream source) throws ImportException {
    StringWriter writer = new StringWriter();
    try {
      byte[] byteArray = IOUtils.toByteArray(source);
      validateAgainstXSD(new ByteArrayInputStream(byteArray));
      IOUtils.copy(new ByteArrayInputStream(byteArray), writer, INPUT_ENCODING);
      String inputString = writer.toString();
      Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder()
          .parse(new InputSource(new StringReader(inputString)));
      return doImportFromXmlNode(doc.getDocumentElement());
    } catch (SAXException | IOException | ParserConfigurationException | URISyntaxException e) {
      throw new ImportException(e);
    }
  }

  public abstract T doImportFromXmlNode(Node source) throws ImportException;

  protected abstract String getXSDFilePath() throws URISyntaxException;
}
