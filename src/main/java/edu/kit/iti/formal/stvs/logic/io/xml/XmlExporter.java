package edu.kit.iti.formal.stvs.logic.io.xml;


import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;
import org.w3c.dom.Node;

import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.StringWriter;

/**
 * @author Benjamin Alt
 */
public abstract class XmlExporter<F> implements Exporter<F> {

  public OutputStream export(F source) throws ExportException {
    Node xmlNode = exportToXmlNode(source);
    StringWriter writer = new StringWriter();
    try {
      Transformer transformer = TransformerFactory.newInstance().newTransformer();
      transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
      transformer.transform(new DOMSource(xmlNode), new StreamResult(writer));
      String xmlString = writer.toString();
      ByteArrayOutputStream stream = new ByteArrayOutputStream();
      stream.write(xmlString.getBytes());
      return stream;
    } catch (TransformerException | IOException e) {
        throw new ExportException(e);
    }
  }

  public abstract Node exportToXmlNode(F source);
}
