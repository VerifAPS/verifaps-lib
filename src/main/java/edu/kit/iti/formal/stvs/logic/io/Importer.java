package edu.kit.iti.formal.stvs.logic.io;

import java.io.InputStream;

/**
 * Created by bal on 11.01.17.
 */
public interface Importer <T> {
    public T doImport(InputStream source) throws ImportException;
}
