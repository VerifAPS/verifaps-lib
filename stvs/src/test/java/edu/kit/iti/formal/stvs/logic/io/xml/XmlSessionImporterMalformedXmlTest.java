package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.config.*;
import edu.kit.iti.formal.stvs.model.config.History;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Benjamin Alt
 */
@RunWith(Parameterized.class)
public class XmlSessionImporterMalformedXmlTest {
  private File file;

  @Parameterized.Parameters
  public static Collection<File> testFiles() throws URISyntaxException {
    List<File> testFiles = new ArrayList<>();
    for (int i = 1; i < 6; i++) {
      testFiles.add(new File(XmlConstraintSpecImporter.class.getResource(
          "session_invalid_xml_" + i + ".xml").toURI().getPath()));
    }
    return testFiles;
  }

  public XmlSessionImporterMalformedXmlTest(File input) {
    this.file = input;
  }

  /**
   * Test whether importing malformed XML throws ImportExceptions.
   */
  @Test(expected=ImportException.class)
  public void sessionImporterMalformedXmlTest() throws URISyntaxException, ImportException,
      IOException, ExportException {
      ImporterFacade.importSession(file, ImporterFacade.ImportFormat.XML, new GlobalConfig(), new
          History());
  }
}
