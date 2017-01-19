package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;

import java.io.InputStream;

/**
 * Created by bal on 11.01.17.
 */
public class XmlSessionImporter extends XmlImporter<StvsRootModel> {

  @Override
  public StvsRootModel doImport(InputStream source) throws ImportException {
    return null;
  }
}
