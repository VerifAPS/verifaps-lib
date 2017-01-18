package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;

import java.io.InputStream;

/**
 * Created by bal on 11.01.17.
 */
public class XmlConfigImporter extends XmlImporter<GlobalConfig> {

  @Override
  public GlobalConfig doImport(InputStream source) throws ImportException {
    return null;
  }
}
