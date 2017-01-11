package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import jdk.nashorn.internal.objects.Global;
import org.w3c.dom.Node;

import java.io.InputStream;

/**
 * Created by bal on 11.01.17.
 */
public class XMLConfigImporter extends XMLImporter<GlobalConfig> {

    @Override
    public GlobalConfig doImport(InputStream source) throws ImportException {
        return null;
    }
}
