package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.io._1.Config;
import edu.kit.iti.formal.stvs.io._1.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.math.BigInteger;

/**
 * This class provides the functionality to export a {@link GlobalConfig} object to an xml node.
 *
 * @author Benjamin Alt
 */
public class XmlConfigExporter extends XmlExporter<GlobalConfig> {

  /**
   * Exports a given {@link GlobalConfig} as a XML {@link Node}.
   *
   * @param source Global config that should be exported
   * @return The XML Node representing the global config
   * @throws ExportException Exception while marshalling
   */
  @Override
  public Node exportToXmlNode(GlobalConfig source) throws ExportException {
    ObjectFactory objectFactory = new ObjectFactory();
    Config.General general = objectFactory.createConfigGeneral();
    general.setUiLanguage(source.getUiLanguage());
    general.setSimulationTimeout(new BigInteger(Integer.toString(source.getSimulationTimeout())));
    general
        .setVerificationTimeout(new BigInteger(Integer.toString(source.getVerificationTimeout())));
    general.setMaxLineRollout(new BigInteger(Integer.toString(source.getMaxLineRollout())));
    Config.General.WindowSize windowSize = objectFactory.createConfigGeneralWindowSize();
    windowSize.setHeight(new BigInteger(Integer.toString(source.getWindowHeight())));
    windowSize.setWidth(new BigInteger(Integer.toString(source.getWindowWidth())));
    windowSize.setMaximized(source.isWindowMaximized());
    general.setWindowSize(windowSize);
    Config config = objectFactory.createConfig();
    config.setGeneral(general);
    Config.Editor editor = objectFactory.createConfigEditor();
    editor.setFontFamily(source.getEditorFontFamily());
    editor.setFontSize(new BigInteger(Integer.toString(source.getEditorFontSize())));
    editor.setShowLineNumbers(source.getShowLineNumbers());
    config.setEditor(editor);
    Config.Dependencies deps = objectFactory.createConfigDependencies();
    deps.setZ3Path(source.getZ3Path());
    deps.setNuxmvFilename(source.getNuxmvFilename());
    deps.setGetetaCommand(source.getGetetaCommand());
    config.setDependencies(deps);
    JAXBElement<Config> element = objectFactory.createConfig(config);
    return marshalToNode(element, NAMESPACE);
  }
}
