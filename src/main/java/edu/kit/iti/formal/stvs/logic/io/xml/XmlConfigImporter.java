package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.net.URISyntaxException;

/**
 * @author Benjamin Alt
 */
public class XmlConfigImporter extends XmlImporter<GlobalConfig> {

  @Override
  public GlobalConfig doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Config importedConfig = ((JAXBElement<Config>) jaxbUnmarshaller.unmarshal(source)).getValue();
      GlobalConfig config = new GlobalConfig();
      Config.General general = importedConfig.getGeneral();
      if (general != null) {
        if (general.getUiLanguage() != null) {
          config.setUiLanguage(general.getUiLanguage());
        }
        if (general.getSimulationTimeout() != null) {
          config.setSimulationTimeout(general.getSimulationTimeout().intValue());
        }
        if (general.getVerificationTimeout() != null) {
          config.setVerificationTimeout(general.getVerificationTimeout().intValue());
        }
        if (general.getWindowSize().getHeight() != null) {
          config.setWindowHeight(general.getWindowSize().getHeight().intValue());
        }
        if (general.getWindowSize().getWidth() != null) {
          config.setWindowWidth(general.getWindowSize().getWidth().intValue());
        }
        if (general.getMaxLineRollout() != null) {
          config.setMaxLineRollout(general.getMaxLineRollout().intValue());
        }
      }
      Config.Editor editor = importedConfig.getEditor();
      if (editor != null) {
        if (editor.getFontSize() != null) {
          config.setEditorFontSize(editor.getFontSize().intValue());
        }
        if (editor.getFontFamily() != null) {
          config.setEditorFontFamily(editor.getFontFamily());
        }
        config.setShowLineNumbers(editor.isShowLineNumbers());
      }
      Config.Dependencies deps = importedConfig.getDependencies();
      if (deps != null) {
        if (deps.getGetetaCommand() != null) {
          config.setGetetaCommand(deps.getGetetaCommand());
        }
        if (deps.getNuxmvFilename() != null) {
          config.setNuxmvFilename(deps.getNuxmvFilename());
        }
        if (deps.getZ3Path() != null) {
          config.setZ3Path(deps.getZ3Path());
        }
      }
      return config;
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/config.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}