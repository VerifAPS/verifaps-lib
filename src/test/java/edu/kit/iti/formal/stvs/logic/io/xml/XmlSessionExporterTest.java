package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;

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
    // TODO: AssertEquals
  }
}