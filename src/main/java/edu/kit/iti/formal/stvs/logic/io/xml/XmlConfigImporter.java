package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;

import java.io.File;
import java.net.URISyntaxException;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.w3c.dom.Node;

/**
 * This class provides the functionality to import a {@link GlobalConfig} from a xml node.
 *
 * @author Benjamin Alt
 */
public class  XmlConfigImporter extends XmlImporter<GlobalConfig> {

  /**
   * Imports a {@link GlobalConfig} from a xml {@link Node}.
   *
   * @param source Xml node that should be imported
   * @return Imported config
   * @throws ImportException Exception while importing
   */
  @Override
  public GlobalConfig doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Config importedConfig = ((JAXBElement<Config>) jaxbUnmarshaller.unmarshal(source)).getValue();
      GlobalConfig config = new GlobalConfig();
      setGeneralSettings(importedConfig.getGeneral(), config);
      setEditorSettings(importedConfig.getEditor(), config);
      setDependencies(importedConfig.getDependencies(), config);
      return config;
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Set the dependencies section of a given {@link GlobalConfig} according to an imported
   * {@link edu.kit.iti.formal.stvs.logic.io.xml.Config.Dependencies} object.
   * @param deps The imported dependencies
   * @param config The config to modify
   */
  private void setDependencies(Config.Dependencies deps, GlobalConfig config) {
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
  }

  /**
   * Set the "general" section of a given {@link GlobalConfig} according to an imported
   * {@link edu.kit.iti.formal.stvs.logic.io.xml.Config.General} object.
   * @param general The imported {@link edu.kit.iti.formal.stvs.logic.io.xml.Config.General} object
   * @param config The config to modify
   */
  private void setGeneralSettings(Config.General general, GlobalConfig config) {
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
      if (general.getWindowSize().isMaximized() != null) {
        config.setWindowMaximized(general.getWindowSize().isMaximized());
      }
      if (general.getMaxLineRollout() != null) {
        config.setMaxLineRollout(general.getMaxLineRollout().intValue());
      }
    }
  }

  /**
   * Set the "editor" section of a given {@link GlobalConfig} according to an imported
   * {@link edu.kit.iti.formal.stvs.logic.io.xml.Config.Editor} object.
   * @param editor The imported {@link edu.kit.iti.formal.stvs.logic.io.xml.Config.Editor} object
   * @param config The config to modify
   */
  private void setEditorSettings(Config.Editor editor, GlobalConfig config) {
    if (editor != null) {
      if (editor.getFontSize() != null) {
        config.setEditorFontSize(editor.getFontSize().intValue());
      }
      if (editor.getFontFamily() != null) {
        config.setEditorFontFamily(editor.getFontFamily());
      }
      config.setShowLineNumbers(editor.isShowLineNumbers());
    }
  }

  @Override
  protected String getXsdFilePath() throws URISyntaxException {
    File xsdFile = new File(this.getClass().getResource("/fileFormats/config.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}
