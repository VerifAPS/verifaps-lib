package edu.kit.iti.formal.stvs.logic.io.xml;

import static org.junit.Assert.assertEquals;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import java.io.ByteArrayOutputStream;
import java.io.File;

import org.apache.commons.io.FileUtils;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Benjamin Alt
 */
public class XmlSessionExporterTest {

  private XmlSessionExporter exporter;

  @Before
  public void setUp() {
    exporter = new XmlSessionExporter();
  }

  @Test
  public void exportDefault() throws Exception {
    ByteArrayOutputStream result = exporter.export(new StvsRootModel());
    String resultString = new String(result.toByteArray(), "utf-8");
    String expectedString = FileUtils.readFileToString(new File(this.getClass().getResource
        ("session_empty.xml").toURI()), "utf-8");
    assertEquals(TestUtils.removeWhitespace(expectedString), TestUtils.removeWhitespace
        (resultString));
  }
}