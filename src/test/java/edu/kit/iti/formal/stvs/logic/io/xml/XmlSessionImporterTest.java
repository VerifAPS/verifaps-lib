package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.*;
import edu.kit.iti.formal.stvs.model.config.History;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

/**
 * Created by bal on 05.02.17.
 */
public class XmlSessionImporterTest {

  private XmlSessionImporter importer;

  @Before
  public void setUp() throws ImportException {
    importer = new XmlSessionImporter(new GlobalConfig(), new History());
  }

  @Test
  public void doImport() throws Exception {
    StvsRootModel importedSession = ImporterFacade.importSession(new File(this.getClass()
        .getResource
        ("session_valid_1.xml").toURI().getPath()), ImporterFacade.ImportFormat.XML, new
        GlobalConfig(), new History());
    System.out.println();
  }

}