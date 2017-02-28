package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.Importer;
import org.apache.commons.io.IOUtils;
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
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.net.URISyntaxException;

/**
 * Common superclass for all Importers that import from xml.
 *
 * @author Benjamin Alt
 */
public abstract class XmlImporter<T> implements Importer<T> {
  private static final String INPUT_ENCODING = "utf8";

  /**
   * Checks that the given input matches the definition defined by {@code getXsdFilePath()}.
   *
   * @param xml Stream that holds the xml to be validated
   * @throws SAXException       A general xml exception
   * @throws IOException        Error while communicating with IO while validating
   * @throws URISyntaxException could not parse uri to xsd file
   */
  private void validateAgainstXsd(InputStream xml)
      throws SAXException, IOException, URISyntaxException {
    SchemaFactory factory =
        SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
    Schema schema = factory.newSchema(new File(getXsdFilePath()));
    Validator validator = schema.newValidator();
    validator.validate(new StreamSource(xml));
  }

  /**
   * Imports an object from a xml input stream.
   *
   * @param source Stream that holds the xml to be validated
   * @return Imported object
   * @throws ImportException Exception while importing
   */
  public T doImport(InputStream source) throws ImportException {
    StringWriter writer = new StringWriter();
    try {
      byte[] byteArray = IOUtils.toByteArray(source);
      validateAgainstXsd(new ByteArrayInputStream(byteArray));
      IOUtils.copy(new ByteArrayInputStream(byteArray), writer, INPUT_ENCODING);
      String inputString = writer.toString();
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      dbf.setNamespaceAware(true);
      Document doc = dbf.newDocumentBuilder()
          .parse(new InputSource(new StringReader(inputString)));
      return doImportFromXmlNode(doc.getDocumentElement());
    } catch (SAXException | IOException | ParserConfigurationException | URISyntaxException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Must be implemented by subclasses.
   * This method must provide the logic to convert the given {@code source} {@link Node} into
   * the corresponding object.
   *
   * @param source Node to import
   * @return imported object
   * @throws ImportException Exception while importing
   */
  public abstract T doImportFromXmlNode(Node source) throws ImportException;

  /**
   * Must be implemented by subclasses.
   * This method must provide the logic to get the path to the xsd file this
   * importer should use to check its input against.
   *
   * @return Path to the xsd
   * @throws URISyntaxException could not parse uri to xsd file
   */
  protected abstract String getXsdFilePath() throws URISyntaxException;
}
