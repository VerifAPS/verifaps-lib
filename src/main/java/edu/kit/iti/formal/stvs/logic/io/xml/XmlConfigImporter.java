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
      Config.Editor editor = importedConfig.getEditor();
      config.setUiLanguage(general.getUiLanguage());
      config.setSimulationTimeout(general.getSimulationTimeout().intValue());
      config.setVerificationTimeout(general.getVerificationTimeout().intValue());
      config.setWindowHeight(general.getWindowSize().getHeight().intValue());
      config.setWindowWidth(general.getWindowSize().getWidth().intValue());
      config.setEditorFontSize(editor.getFontSize().intValue());
      config.setEditorFontFamily(editor.getFontFamily());
      config.setShowLineNumbers(editor.isShowLineNumbers());
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