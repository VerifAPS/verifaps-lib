package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class XmlConfigExporterTest {

  private XmlConfigExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlConfigExporter();
  }

  @Test
  public void testExportConstraintDefault() throws Exception {
    ByteArrayOutputStream result = exporter.export(new GlobalConfig());
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = TestUtils.readFileToString(this.getClass().getResource("config_valid_default" +
        ".xml").getPath());
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace
        (resultString));
  }

}