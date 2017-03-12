package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.URISyntaxException;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConfigImporterTest {

  private XmlConfigImporter importer;

  @Before
  public void setUp() {
    importer = new XmlConfigImporter();
  }

  @Test
  public void testDoImport() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (XmlConfigImporter.class.getResource("config_valid_nodeps.xml").toURI()));
    GlobalConfig config = importer.doImport(inputStream);
    assertEquals("EN", config.getUiLanguage());
    assertEquals(100, config.getVerificationTimeout());
    assertEquals(100, config.getSimulationTimeout());
    assertEquals("Comic Sans", config.getEditorFontFamily());
    assertEquals(12, config.getEditorFontSize());
    assertEquals(true, config.getShowLineNumbers());
  }

  @Test
  public void testDoImportDefault() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("/edu/kit/iti/formal/stvs/logic/io/xml/config_valid_default" +
            ".xml").toURI()));
    GlobalConfig actualConfig = importer.doImport(inputStream);
    GlobalConfig expectedConfig = new GlobalConfig();
    assertEquals(expectedConfig, actualConfig);
  }

  @Test(expected = ImportException.class)
  public void testDoImportInvalidData() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("config_invalid_1.xml").toURI()));
    GlobalConfig config = importer.doImport(inputStream);
  }
}