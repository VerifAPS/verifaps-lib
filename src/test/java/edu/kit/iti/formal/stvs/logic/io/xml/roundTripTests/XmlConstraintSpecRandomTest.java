package edu.kit.iti.formal.stvs.logic.io.xml.roundTripTests;

import edu.kit.iti.formal.stvs.RandomTest;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.RandomGenerator;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import org.apache.commons.io.FileUtils;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static junit.framework.TestCase.assertEquals;

/**
 * Created by bal on 02.03.17.
 */
@Category(RandomTest.class)
public class XmlConstraintSpecRandomTest {
  private final int MAX_COLUMNS = 100;
  private final int MAX_ROWS = 100;
  private final int MAX_FREE_VARIABLES = 3;
  private RandomGenerator generator;

  @Before
  public void setUp() {
    generator = new RandomGenerator(100);
  }

  @Test
  public void testRandomAll() throws IOException, ExportException, ImportException {
    for (int columns = 1; columns <= MAX_COLUMNS; columns += 10) {
      for (int rows = 0; rows <= MAX_ROWS; rows += 10) {
        for (int freeVariables = 0; freeVariables <= MAX_FREE_VARIABLES; freeVariables++) {
          System.out.format("Testing random %d %d %d %n", columns, rows, freeVariables);
          testRandom(columns, rows, freeVariables);
        }
      }
    }
  }

  private void testRandom(int columns, int rows, int freeVariables) throws IOException, ExportException, ImportException {
    File tempFile = File.createTempFile("randomTest", "");
    ConstraintSpecification originalSpec = generator.randomConstraintSpec(columns, rows,
        freeVariables);
    ExporterFacade.exportSpec(originalSpec, ExporterFacade.ExportFormat.XML, tempFile);
      String originalFileContents = FileUtils.readFileToString(tempFile, "utf-8");
      ConstraintSpecification importedSpec = ImporterFacade.importConstraintSpec(tempFile,
        ImporterFacade.ImportFormat.XML);
    assertEquals(originalSpec, importedSpec);
    ExporterFacade.exportSpec(importedSpec, ExporterFacade.ExportFormat.XML, tempFile);
    String reexportedFileContents = FileUtils.readFileToString(tempFile, "utf-8");
    assertEquals(originalFileContents, reexportedFileContents);
  }

  private void testRandomModelToModel(int columns, int rows, int freeVariables) {

  }
}
