package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringWriter;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Node;

/**
 * Common superclass for all Exporters that export to xml.
 *
 * @author Benjamin Alt
 */
public abstract class XmlExporter<F> implements Exporter<F> {

  public static String NAMESPACE = "edu.kit.iti.formal.stvs.logic.io.xml";

  /**
   * Exports an Object as xml.
   *
   * @param source Object to export
   * @return The output xml is written to this stream
   * @throws ExportException Exception while exporting
   */
  public ByteArrayOutputStream export(F source) throws ExportException {
    Node xmlNode = exportToXmlNode(source);
    StringWriter writer = new StringWriter();
    try {
      Transformer transformer = TransformerFactory.newInstance().newTransformer();
      transformer.setOutputProperty(OutputKeys.INDENT, "yes");
      transformer.transform(new DOMSource(xmlNode), new StreamResult(writer));
      String xmlString = writer.toString();
      ByteArrayOutputStream stream = new ByteArrayOutputStream();
      stream.write(xmlString.getBytes());
      return stream;
    } catch (TransformerException | IOException e) {
      throw new ExportException(e);
    }
  }

  /**
   * Marshals a {@link JAXBElement} to a xml node.
   *
   * @param element The element that should be marshaled
   * @param namespace Xml namespace used in the exported node
   * @return Node representing the input {@code element}
   * @throws ExportException Exception while exporting
   */
  protected static Node marshalToNode(JAXBElement element, String namespace)
      throws ExportException {
    try {
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document document = db.newDocument();
      JAXBContext context = JAXBContext.newInstance(namespace);
      Marshaller marshaller = context.createMarshaller();
      marshaller.setProperty("jaxb.formatted.output", Boolean.TRUE);
      marshaller.marshal(element, document);
      return document.getDocumentElement();
    } catch (ParserConfigurationException | JAXBException e) {
      throw new ExportException(e);
    }
  }

  /**
   * Must be implemented by subclasses. This method must provide the logic to convert the given
   * {@code source} object into a xml {@link Node}
   *
   * @param source Element that should be converted
   * @return Xml node
   * @throws ExportException Exception while exporting
   */
  public abstract Node exportToXmlNode(F source) throws ExportException;
}
