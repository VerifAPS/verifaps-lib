package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Collection;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
 @RunWith(Parameterized.class)
 public class XmlSessionRoundtripTest {
  private File file;

  @Parameterized.Parameters
  public static Collection<File> testFiles() throws URISyntaxException {
    return TestUtils.getTestFiles(TestUtils.FileType.SESSION, TestUtils.Status.VALID);
  }

  public XmlSessionRoundtripTest(File input) {
    this.file = input;
  }

  @Test
  public void sessionRoundtripTest() throws URISyntaxException, ImportException,
      IOException, ExportException {
    String fileContentsBefore = TestUtils.readFromFile(file.getAbsolutePath());
    StvsRootModel importedSession = ImporterFacade.importSession(file,
        ImporterFacade.ImportFormat.XML, new GlobalConfig(), new History());
    File tempFile = File.createTempFile("test", "");
    ExporterFacade.exportSession(importedSession, ExporterFacade.ExportFormat.XML, tempFile);
    String fileContentsAfter = TestUtils.readFromFile(tempFile.getAbsolutePath());
    assertEquals("ComparisonFailure at file: "+file.getPath(), TestUtils.removeWhitespace
            (fileContentsBefore),
        TestUtils.removeWhitespace(fileContentsAfter));
  }
}