package edu.kit.iti.formal.stvs.logic.io;

import java.io.OutputStream;

/**
 * Created by bal on 11.01.17.
 */
public interface Exporter<F> {
    public OutputStream export(F source);
}
