package edu.kit.iti.formal.smv.printers;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;

/**
 * Write SMV code to a file. {@link #close()} *must be called* to ensure all contents are written.
 * @author Augusto Modanese
 */
public class FilePrinter extends Printer {
    private PrintWriter printWriter;

    public FilePrinter(File file) throws FileNotFoundException {
        printWriter = new PrintWriter(file);
    }

    public FilePrinter(File file, boolean append) throws FileNotFoundException {
        printWriter = new PrintWriter(new FileOutputStream(file, append));
    }

    public void close() {
        printWriter.close();
    }

    @Override
    void print(String s) {
        printWriter.write(s);
    }
}
