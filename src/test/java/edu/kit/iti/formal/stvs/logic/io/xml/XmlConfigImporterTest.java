package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileInputStream;

import static org.junit.Assert.*;

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
        (XmlConfigImporter.class.getResource("/fileFormats/example_config.xml").toURI()));
    GlobalConfig config = importer.doImport(inputStream);
    assertEquals("EN", config.getUiLanguage());
    assertEquals(800, config.getWindowWidth());
    assertEquals(500, config.getWindowHeight());
    assertEquals(100, config.getVerificationTimeout());
    assertEquals(100, config.getSimulationTimeout());
    assertEquals("Comic Sans", config.getEditorFontFamily());
    assertEquals(12, config.getEditorFontSize());
  }

  @Test(expected=ImportException.class)
  public void testDoInvalidImport() throws Exception {
    FileInputStream inputStream = new FileInputStream(new File
        (this.getClass().getResource("example_config_invalid_1.xml").toURI()));
    GlobalConfig config = importer.doImport(inputStream);
  }
}