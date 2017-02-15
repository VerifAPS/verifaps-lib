package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.math.BigInteger;

/**
 * @author Benjamin Alt
 */
public class XmlConfigExporter extends XmlExporter<GlobalConfig> {

  @Override
  public Node exportToXmlNode(GlobalConfig source) throws ExportException {
    ObjectFactory objectFactory = new ObjectFactory();
    Config config = objectFactory.createConfig();
    Config.General general = objectFactory.createConfigGeneral();
    general.setUiLanguage(source.getUiLanguage());
    general.setSimulationTimeout(new BigInteger(Integer.toString(source.getSimulationTimeout())));
    general.setVerificationTimeout(new BigInteger(Integer.toString(source.getVerificationTimeout()
    )));
    general.setMaxLineRollout(new BigInteger(Integer.toString(source.getMaxLineRollout())));
    Config.General.WindowSize windowSize = objectFactory.createConfigGeneralWindowSize();
    general.setWindowSize(windowSize);
    config.setGeneral(general);
    Config.Editor editor = objectFactory.createConfigEditor();
    editor.setFontFamily(source.getEditorFontFamily());
    editor.setFontSize(new BigInteger(Integer.toString(source.getEditorFontSize())));
    editor.setShowLineNumbers(source.getShowLineNumbers());
    config.setEditor(editor);
    Config.Dependencies deps = objectFactory.createConfigDependencies();
    deps.setZ3Path(source.getZ3Path());
    deps.setJavaPath(source.getJavaPath());
    deps.setNuxmvFilename(source.getNuxmvFilename());
    deps.setGetetaFilename(source.getGetetaFilename());
    config.setDependencies(deps);
    JAXBElement<Config> element = objectFactory.createConfig(config);
    return marshalToNode(element);
  }

  public static void main(String[] args) throws ExportException, TransformerException {
    XmlConfigExporter exporter = new XmlConfigExporter();
    Node node = exporter.exportToXmlNode(new GlobalConfig());
    Transformer transformer = TransformerFactory.newInstance().newTransformer();
    transformer.setOutputProperty(OutputKeys.INDENT, "yes");
    DOMSource source = new DOMSource(node);
    StreamResult console = new StreamResult(System.out);
    transformer.transform(source, console);
  }
}
