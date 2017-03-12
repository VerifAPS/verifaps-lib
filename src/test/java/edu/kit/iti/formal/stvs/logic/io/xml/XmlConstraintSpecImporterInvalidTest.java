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
public class XmlConstraintSpecImporterInvalidTest {
  private File file;

  @Parameterized.Parameters
  public static Collection<File> testFiles() throws URISyntaxException {
    List<File> testFiles = new ArrayList<>();
    for (int i = 1; i < 5; i++) {
      testFiles.add(new File(XmlConstraintSpecImporter.class.getResource(
          "spec_constraint_invalid_data_" + i + ".xml").toURI().getPath()));
    }
    return testFiles;
  }

  public XmlConstraintSpecImporterInvalidTest(File input) {
    this.file = input;
  }

  /**
   * Test whether ConstraintSpecifications with invalid data can be imported without throwing
   * exceptions. This must be possible since the user should not be prevented from importing and
   * ConstraintSpecifications containing syntax errors and other invalid data.
   * The conformance of the result of the import with the expected result is assured in other
   * unit tests (see {@link XmlConstraintSpecImporterTest},
   * {@link edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests.XmlConstraintSpecRoundtripTest}).
   */
  @Test
  public void constraintSpecImporterInvalidTest() throws URISyntaxException, ImportException,
      IOException, ExportException {
      ImporterFacade.importConstraintSpec(file, ImporterFacade.ImportFormat.XML);
  }
}
