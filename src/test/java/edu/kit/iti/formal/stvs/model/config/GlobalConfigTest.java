package edu.kit.iti.formal.stvs.model.config;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.*;

/**
 * Created by bal on 26.02.17.
 */
public class GlobalConfigTest {
  private GlobalConfig config;

  @Before
  public void setUp() throws Exception {
    config = ImporterFacade.importConfig(XmlConfigImporter.class.getResourceAsStream
        ("config_valid_complete.xml"), ImporterFacade.ImportFormat.XML);
  }

  @Test
  public void setAll() throws Exception {
    GlobalConfig clone = new GlobalConfig();
    clone.setAll(config);
    assertEquals(clone, config);
  }

  @Test
  public void testEquals() throws Exception {
    GlobalConfig identical = ImporterFacade.importConfig(XmlConfigImporter.class.getResourceAsStream
        ("config_valid_complete.xml"), ImporterFacade.ImportFormat.XML);
    assertEquals(identical, config);
    assertNotEquals(null, config);
    assertEquals(config, config);
    identical.setWindowHeight(1000);
    assertNotEquals(config, identical);
  }

  @Test
  public void testHashCode() throws ImportException {
    GlobalConfig identical = ImporterFacade.importConfig(XmlConfigImporter.class.getResourceAsStream
        ("config_valid_complete.xml"), ImporterFacade.ImportFormat.XML);
    assertEquals(identical.hashCode(), config.hashCode());
    assertEquals(config.hashCode(), config.hashCode());
    identical.setWindowHeight(1000);
    assertNotEquals(config.hashCode(), identical.hashCode());
  }

}