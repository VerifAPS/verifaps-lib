package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Collection;

import static org.junit.Assert.assertEquals;

/**
 * Created by bal on 03.03.17.
 */
@RunWith(Parameterized.class)
public class XmlConfigRoundtripTest {
  private File file;

  @Parameterized.Parameters
  public static Collection<File> testFiles() throws URISyntaxException {
    return TestUtils.getTestFiles(TestUtils.FileType.CONFIG, TestUtils.Status.VALID);
  }

  public XmlConfigRoundtripTest(File input) {
    this.file = input;
  }

  @Test
  public void configRoundtripTest() throws URISyntaxException, ImportException,
      IOException, ExportException {
    String fileContentsBefore = TestUtils.readFromFile(file.getAbsolutePath());
    GlobalConfig importedConfig = ImporterFacade.importConfig(file, ImporterFacade.ImportFormat
        .XML);
    File tempFile = File.createTempFile("test", "");
    ExporterFacade.exportConfig(importedConfig, ExporterFacade.ExportFormat.XML, tempFile);
    String fileContentsAfter = TestUtils.readFromFile(tempFile.getAbsolutePath());
    assertEquals(TestUtils.removeWhitespace(fileContentsBefore),
        TestUtils.removeWhitespace(fileContentsAfter));
  }
}
