package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.io._1.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

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
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringWriter;

/**
 * Common superclass for all Exporters that export to xml.
 *
 * @author Benjamin Alt
 */
public abstract class XmlExporter<F> implements Exporter<F> {

    public static final Class<ObjectFactory> OF_STVS = ObjectFactory.class;
    public static final Class<edu.kit.iti.formal.exteta_1.ObjectFactory> OF_EXTETA = edu.kit.iti.formal.exteta_1.ObjectFactory.class;
    public static final Class<edu.kit.iti.formal.exteta_1_0.report.ObjectFactory> OF_EXTETA_REPORT = edu.kit.iti.formal.exteta_1_0.report.ObjectFactory.class;

    //public static final String NAMESPACE = "http://formal.iti.kit.edu/stvs/io/1.0/";

    /**
     * Marshals a {@link JAXBElement} to a xml node.
     *
     * @param element The element that should be marshaled
     * @param clazz class of the ObjectFactory
     * @return Node representing the input {@code element}
     * @throws ExportException Exception while exporting
     */
    protected static Node marshalToNode(JAXBElement element, Class clazz)
            throws ExportException {
        try {
            DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
            DocumentBuilder db = dbf.newDocumentBuilder();
            Document document = db.newDocument();
            JAXBContext context = JAXBContext.newInstance(clazz);
            Marshaller marshaller = context.createMarshaller();
            marshaller.setProperty("jaxb.formatted.output", Boolean.TRUE);
            marshaller.marshal(element, document);
            return document.getDocumentElement();
        } catch (ParserConfigurationException | JAXBException e) {
            throw new ExportException(e);
        }
    }

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
            stream.write(xmlString.getBytes("utf-8"));
            return stream;
        } catch (TransformerException | IOException e) {
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
