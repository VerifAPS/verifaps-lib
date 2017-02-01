package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import java.io.File;
import java.net.URISyntaxException;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Consumer;

/**
 * @author Benjamin Alt
 */
public class XmlConfigImporter extends XmlImporter<GlobalConfig> {

  private final Map<String, Consumer<String>> setters;
  GlobalConfig config;

  public XmlConfigImporter() {
    config = new GlobalConfig();
    setters = new HashMap<>();
    setters.put("uiLanguage", (String val) -> config.setUiLanguage(val));
    setters.put("width", (String val) -> config.setWindowWidth(Integer.parseInt(val)));
    setters.put("height", (String val) -> config.setWindowHeight(Integer.parseInt(val)));
    setters.put("verificationTimeout", (String val) -> config.setVerificationTimeout(
        Integer.parseInt(val)));
    setters.put("simulationTimeout", (String val) -> config.setSimulationTimeout(
        Integer.parseInt(val)));
    setters.put("showLineNumbers", (String val) -> config.setShowLineNumbers(
        Boolean.parseBoolean(val)));
    setters.put("fontFamily", (String val) -> config.setEditorFontFamily(val));
    setters.put("fontSize", (String val) -> config.setEditorFontSize(Integer.parseInt(val)));
  }

  @Override
  public GlobalConfig doImportFromXmlNode(Node source) throws ImportException {
    config = new GlobalConfig();
    NodeList childNodes = source.getChildNodes();
    try {
      for (int i = 0; i < childNodes.getLength(); i++) {
        Node child = childNodes.item(i);
        if (child.getNodeName().equals("general")) {
          importGeneral(child);
        } else if (child.getNodeName().equals("editor")) {
          importEditor(child);
        }
      }
    } catch (IllegalArgumentException e) {
      throw new ImportException(e);
    }
    return config;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/config.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }

  private void importGeneral(Node general) throws ImportException {
    NodeList generalChildNodes = general.getChildNodes();
    for (int j = 0; j < generalChildNodes.getLength(); j++) {
      Node generalChild = generalChildNodes.item(j);
      String nodeName = generalChild.getNodeName();
      if (setters.containsKey(nodeName)) {
        setters.get(nodeName).accept(generalChild.getTextContent());
      } else if (nodeName.equals("windowSize")) {
        NodeList windowChildNodes = generalChild.getChildNodes();
        for (int k = 0; k < windowChildNodes.getLength(); k++) {
          Node windowChild = windowChildNodes.item(k);
          if (setters.containsKey(windowChild.getNodeName())) {
            setters.get(windowChild.getNodeName()).accept(windowChild.getTextContent());
          } else if (windowChild.getNodeType() == Node.ELEMENT_NODE) {
            throw new ImportException("Invalid node name: " + windowChild.getNodeName());
          }
        }
      } else if (generalChild.getNodeType() == Node.ELEMENT_NODE) {
        throw new ImportException("Invalid node name: " + generalChild.getNodeName());
      }
    }
  }

  private void importEditor(Node editor) throws ImportException {
    NodeList editorChildNodes = editor.getChildNodes();
    for (int j = 0; j < editorChildNodes.getLength(); j++) {
      Node editorChild = editorChildNodes.item(j);
      String nodeName = editorChild.getNodeName();
      if (setters.containsKey(nodeName)) {
        setters.get(nodeName).accept(editorChild.getTextContent());
      } else if (editorChild.getNodeType() == Node.ELEMENT_NODE) {
        throw new ImportException("Invalid node name: " + editorChild.getNodeName());
      }
    }
  }
}