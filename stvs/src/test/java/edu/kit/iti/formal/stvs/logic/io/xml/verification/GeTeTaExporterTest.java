package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.TestUtils;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.nio.file.Paths;

import static org.junit.Assert.assertEquals;

/**
 * @author Benjamin Alt
 */
public class GeTeTaExporterTest {
    @Test
    public void testExport() throws ImportException, IOException, ExportException, URISyntaxException {
        InputStream stream = StvsApplication.class.getResourceAsStream("testSets/valid_1/constraint_spec_valid_1.xml");
        ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(
                stream, ImporterFacade.ImportFormat.XML);
        File tempFile = File.createTempFile("test", "");
        ExporterFacade.exportSpec(constraintSpec, ExporterFacade.ExportFormat.GETETA, tempFile);
        String expectedString = TestUtils.readFromFile(
                Paths.get(StvsApplication.class.getResource("testSets/valid_1/geteta_input_valid_1.xml").toURI()).toString());
        String actualString = TestUtils.readFromFile(tempFile.getAbsolutePath());
        assertEquals(
                TestUtils.removeWhitespace(expectedString),
                TestUtils.removeWhitespace(actualString));
    }
}