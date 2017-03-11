package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
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
public class XmlConstraintSpecImporterMalformedXmlTest {
  private File file;

  @Parameterized.Parameters
  public static Collection<File> testFiles() throws URISyntaxException {
    List<File> testFiles = new ArrayList<>();
    for (int i = 1; i < 7; i++) {
      testFiles.add(new File(XmlConstraintSpecImporter.class.getResource(
          "spec_constraint_invalid_xml_" + i + ".xml").toURI().getPath()));
    }
    return testFiles;
  }

  public XmlConstraintSpecImporterMalformedXmlTest(File input) {
    this.file = input;
  }

  /**
   * Test whether importing malformed XML throws ImportExceptions.
   */
  @Test(expected=ImportException.class)
  public void constraintSpecImporterInvalidTest() throws URISyntaxException, ImportException,
      IOException, ExportException {
      ImporterFacade.importConstraintSpec(file, ImporterFacade.ImportFormat.XML);
  }
}
