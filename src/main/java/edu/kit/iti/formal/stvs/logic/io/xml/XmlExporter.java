package edu.kit.iti.formal.stvs.logic.io.xml;


import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

import javax.swing.text.html.parser.Parser;
import javax.xml.bind.*;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ByteArrayOutputStream;
import java.io.StringWriter;

/**
 * @author Benjamin Alt
 */
public abstract class XmlExporter<F> implements Exporter<F> {

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

  protected static Node marshalToNode(JAXBElement element) throws ExportException {
    try {
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document document = db.newDocument();
      JAXBContext context = JAXBContext.newInstance("edu.kit.iti.formal.stvs.logic.io.xml");
      Marshaller marshaller = context.createMarshaller();
      marshaller.setProperty("jaxb.formatted.output", Boolean.TRUE);
      marshaller.marshal(element, document);
      return document.getDocumentElement();
    } catch (ParserConfigurationException | JAXBException e) {
      throw new ExportException(e);
    }
  }

  public abstract Node exportToXmlNode(F source) throws ExportException;
}
